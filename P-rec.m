(* ::Package:: *)

(*
######################
Compute first few terms of P-recursive sequence
######################
*)
Rec2Seq[L_, n_, N_, inival_, K_] := Module[
    {rec, len, ls, i,j},
    
    rec = L2R[L, n, N];
    len = Length[rec];
    If[Length[inival]<len, Print["Not enough initial values"]; Return[{}]];
    
    ls = inival;
    For[i = Length[inival] - len, i <= K - len, i++, 
        ls = Append[ls, Sum[(rec[[j]] /. n -> i)*ls[[i + j]], {j, 1, len}]];
    ];
    
    Return[ls];
]





(*
######################
Detect when fn <= rn <= gn for consecutive terms
######################
*)
FindR[L_, n_, N_, inival_, f_, g_, z_, rho_] := Module[
    {rec, len,rls,i,j,k,l,recval, r},

    rec = L2R[L,n,N];
    len = Length[rec];
    rls = Map[If[inival[[#]]!=0, inival[[# + 1]]/inival[[#]], Infinity] &, 
        Range[1, Length[inival]-1]];
        
    j=0; i=Length[rls]-len+1; recval = Map[rls[[#]] &, Range[i+1, i+len-1]]; 
        
    While[j<len-1,
    
        (* test the bound *)
        If[i<Length[rls], 
            r = rls[[i+1]],
            r = Sum[(rec[[k]]/.n->(i-len+1))/Product[recval[[l]], {l, k, len-1}], {k, 1, len}];
            recval = Append[Delete[recval, 1], r];
        ];
        
        If[N[r-(f/.z->i^(1/rho))]>=0 && N[(g/.z->i^(1/rho))-r]>=0, 
            j++, 
            j=0;
        ];
        i++; 
    ];
    
    Return[i-len+1];

] 










(*
######################
Given an asymptotic expression of an up to K terms, automatically prove the 
Higher Turan inequality
######################
*)
HT[L_, n_, N_, inival_, K_] := Module[
	{rec, t, rho, an, z, un, deg, s, N0=0, i, lb, ub,sl,su},
	
	rec = NormL[L,n,N];
	t = Asy[rec, n, N, K];
	rho = t[[1]][[2]];
	an = t[[1]][[3]][[1]];

	
	(* compute the asymptotic expression of u[i]=a_{n-1} a_{n+1}/ a_n^2 *)
	
	rat = Series[(an /. n -> z^rho + 1)/(an /. n->z^rho), {z, Infinity, 0}];
	deg = Max[0, Exponent[rat, z, Max]];
	rat = Normal[Series[(an /. n -> z^rho + 1)/(an /. n->z^rho), {z, Infinity, K - deg - 1}]];
	
	t = IsBP[L,n,N,(rat/.z->n^(1/rho))];
	If[t[[1]],Print["The sequence is BP"],
		Print["Not a bound preserving sequence: limit = ", t[[2]]]; Return[{False, 0}]];
	
	deg = Exponent[rat, z, Max] - Exponent[rat, z, Min];
	s[1] = Normal[Series[rat/(rat /. z -> (z^rho - 1)^(1/rho)), {z, Infinity, deg}]];
	
    sl = Normal[Series[s[1],{z,Infinity,deg-1}]] - 1/z^(deg-1);
	su = Normal[Series[s[1],{z,Infinity,deg-1}]] + 1/z^(deg-1);
	
	t = RBoundFind1[rat, z, rho, sl, su];
    If[t[[1]],
		Print["We have ", (sl/.z->n^(1/rho)),"<=a_{n+1}a_{n-1}/(a_n)^2<=",(su/.z->n^(1/rho))];
		lb = t[[2]]; ub = t[[3]]; N0 = Max[N0, t[[4]]]; 
			Print[(lb/.z->n^(1/rho)),"<=a_{n+1}/a_n<=",(ub/.z->n^(1/rho))," for n>=", t[[4]]],
		Return[{False, 0}];
	];
	
	
	t = TestR[rec, n, N, lb, ub, z, rho];
	If[t[[1]],
		N0 = Max[N0, t[[2]]];
		Print["a_n preserves the bounds for n>=", t[[2]]]];
		
	i = FindR[L, n, N, inival, lb, ub, z, rho];
	Print["the bounds hold for n>=", i];
	
	Return[{{sl,su}/.z->n^(1/rho), Max[N0, i]}];

]


(*
######################
Given an asymptotic expression of an up to K terms, automatically prove the r-log-convexity
######################
*)
rLogBound[L_, n_, N_, inival_, r_, K_] := Module[
	{rec, t, rho, an, z, rat, deg, s, N0, i, lb, ub},
	
	rec = NormL[L,n,N];
	t = Asy[rec, n, N, K];
	rho = t[[1]][[2]];
	an = t[[1]][[3]][[1]];
	
	(* compute the asymptotic expression of s[i] *)
	
	rat = Series[(an /. n -> z^rho + 1)/(an /. n->z^rho), {z, Infinity, 0}];
	deg = Exponent[rat, z, Max];
	rat = Normal[Series[(an /. n -> z^rho + 1)/(an /. n->z^rho), {z, Infinity, K - deg - 1}]];
	
	t = IsBP[L,n,N,(rat/.z->n^(1/rho))];
	If[Not[t[[1]]],
		Print["Not a bound preserving sequence: limit = ", t[[2]]]; Return[{False, 0}]];
		
	
	deg = Exponent[rat, z, Max] - Exponent[rat, z, Min];
	s[1] = Normal[Series[(rat /. z -> (z^rho + 1)^(1/rho))/rat, {z, Infinity, deg}]];
	
	For[i=2, i<r, i++,
		t = s[i-1]-1; 
		deg = Exponent[t, z, Max] - Exponent[t, z, Min];
		s[i] = Normal[Series[(s[i-1]/.z -> (z^rho + 1)^(1/rho))^2 * 
				t * (t/.z -> (z^rho + 2)^(1/rho)) / (t/.z -> (z^rho + 1)^(1/rho))^2, 
				{z, Infinity, deg}]];
	];
 
	(* compute the bounds for s *)	
	lb = 1; ub = Infinity; N0 = 0;
	For[i=1, i<r, i++,
		t = SBoundFind[s[r-i], z, rho, lb, ub];
		If[t[[1]], 
			lb = t[[2]]; ub = t[[3]]; N0 = Max[N0, t[[4]]];
				Print[(lb/.z->n^(1/rho)),"<=s[",r-i,"]<=",(ub/.z->n^(1/rho))," for n>=", t[[4]]],
			Return[{False, 0}];
		];
	];
	
	t = RBoundFind[rat, z, rho, lb, ub];
	If[t[[1]],
		lb = t[[2]]; ub = t[[3]]; N0 = Max[N0, t[[4]]];
			Print[(lb/.z->n^(1/rho)),"<=a_{n+1}/a_n<=",(ub/.z->n^(1/rho))," for n>=", t[[4]]],
		Return[{False, 0}];
	];
	
	
	t = TestR[rec, n, N, lb, ub, z, rho];
	If[t[[1]],
		N0 = Max[N0, t[[2]]];
		Print["a_n preserves the bounds for n>=", t[[2]]]];
		
	i = FindR[L, n, N, inival, lb, ub, z, rho];
	Print["the bounds hold for n>=", i];
	
	Return[{t[[1]], Max[N0, i]}];

]

(*
######################
Compute the leading term of polynomial
######################
*)
Lcoeff[p_, x_] := Module[
	{pow},
	
	pow = Exponent[p, x, Max];
	Return[Coefficient[p, x, pow]];
]


(*
######################
Compute the parameter mu and lambda in the asymptotic expression of a P-recursive sequence
a_n = (n/e)^mu lambda^n
The output is a set of quartiples {mu, lambda, multiple, maxdeg}
######################
*)
EstMu[L_, n_, N_] :=Module[
	{rec, cls, i,j, t, len, val, re, triset, m, s, lambda, mu},
	
	rec = NormL[L, n, N];
	cls = {};
	
	For[i=0, i<=Exponent[rec, N, Max], i++,
		t = Together[Coefficient[rec, N, i]];
		cls = Append[cls, i*mu + Exponent[Numerator[t], n, Max] - Exponent[Denominator[t], n, Max]];
	];
		
	(* We try to find mu such that cls has two maximal values.
	For this purpose, we assume cls[i] is maximal and try the boundary values *)
	
	len = Length[cls];
	val = {};
	For[i=1, i<=len, i++,
		re = Reduce[Map[cls[[i]]>=cls[[#]] &, Range[1, len]]];
		val = Join[val, Select[Map[re[[#]] &, Range[1, Length[re]]], NumberQ]]
	];  
	val = DeleteDuplicates[val];
	
	(* We try to find lambda such that the leading term in the series expansion
	 of n^* vanished *)
	
	quadset = {};
	
	For[i=1, i<=Length[val], i++,
	 	
		m = Max[cls /. mu -> val[[i]]];
	 	s = 0;
	 	For[j=1, j<=len, j++,
	 		If[(cls[[j]] /. mu -> val[[i]]) == m,
	 			t = Together[Coefficient[rec, N, j-1]]; 
	 			s = s + lambda^(j-1) * Lcoeff[Numerator[t], n]/Lcoeff[Denominator[t], n];
	 		];
	 	];
	 	
	 	s = Expand[s/lambda^Exponent[s,lambda,Min]];

	 	re = Solve[s == 0, lambda];
	 	t = DeleteDuplicates[re];
	 	
	 	For[j=1, j<=Length[t], j++,
		 	(* rho is the lcm of the denominator of mu and the multiple of the root lambda *)
	 		quadset = Append[quadset, {val[[i]], lambda/. t[[j]], Count[re, t[[j]]], m}];
	 	];
	 ];
	 	
	 Return[quadset];
]	 			

(* 
recurrence examples 
1. with log : L = (n + b)^2 - (n + 1) (2 n + 2 b + 1) N + (n + 1) (n + 2) N^2;
2. multiple=1 but val=1/2: L = x + (n + 2) N - 2 N^3;
3. val=1 but multiple=2: 
	L = 1 - (2*n - 1)/N + (n - 1)*(n - 2)/N^2 
		+ (n - 1)*(n - 2)/N^3 - (1/2*(n - 1))*(n - 2)*(n - 3)/N^4
*)







(*
######################
Compute the asymptotic expression of a P-recursive sequence (no-log involved)
######################
*)
Asy[L_, n_, N_, K_, MaxOnly_: True] := Module[
	{rec, muls, mu, i,j,k, lambda, rho, alpha, theta, b, f, s, deg, an, spol, z, sol, re,mul},
	
	rec = NormL[L, n, N];
	
	muls = FullSimplify[EstMu[rec, n, N]]; 

	If[MaxOnly, 
		mu = Max[Map[N[Abs[#[[1]]]] &, muls]];
		muls = Select[muls, N[Abs[#[[1]]-mu]]<0.0001 &];
		lambda = Max[Map[N[Abs[#[[2]]]] &, muls]];
		muls = Select[muls, N[Abs[#[[2]]-lambda]]<0.0001 &]
	];
		
	re = {};
	For[i=1, i<=Length[muls], i++,
		{mu, lambda, mul, deg} = muls[[i]];
        rho = LCM[mul, Denominator[mu]];		
		deg = deg-1;
		
        f = 1 + Sum[b[j]*n^(-j/rho), {j,1,K}];
		g =(n/Exp[1])^(mu*n) * lambda^n * Exp[Sum[alpha[j]*n^(j/rho), {j,1,rho-1}]] * n^theta; 
		s = Sum[Coefficient[rec, N, j] * (1+j/n)^(mu*n) * (n+j)^(mu*j) * Exp[-mu*j] * lambda^j 
                * Exp[Sum[alpha[k]*((z^rho+j)^(k/rho)-z^k), {k,1,rho-1}]] * (1+j/n)^theta
				* (f/.n->n+j)/f, {j,0,Exponent[rec,N,Max]}];
		
		For[j=-rho, j<rho, j++,
				spol = Map[Series[#/.n->z^rho, {z, Infinity, -rho*deg + K + rho + j}] &, s];
				powls = Exponent[spol, z, List]; 
				
				sol = Solve[Map[Coefficient[spol, z, #]==0 &, powls], 
					Join[Map[alpha[#] &, Range[1,rho-1]], Map[b[#] &, Range[1,K]], {theta}]];
				
				If[(sol != {}) && (Not[(b[K]/.sol[[1]]) === b[K]]), Break[]];
		];
		
		re = Append[re, {mul, rho, Map[(g/.#) * Map[FullSimplify, (f/.#)] &, sol]}];
		
	];
	
	Return[re];
]







(*
######################
Given an asymptotic expression of the ratio a_{n+1}/a_n,
compute the asymptotic expressions of s[i] for 1 <= i <= r
######################
*)

ComputS[rat_, z_, rho_, r_:1] := Module[
	{m, sls, i, t},
	
	(* compute s[1] *)
	m = Exponent[rat, z, Max] - Exponent[rat, z, Min];
	sls = {Normal[ Series[(rat /. z->(z^rho+1)^(1/rho))/rat, {z, Infinity, m}] ]}; 
	
	
	(* compute s[i] for 2 <= i <= r *)
	For[i=2, i<=r, i++,
		t = sls[[i-1]]-1;
		
		(* we require that the result contains at least 2 terms, i.e., 1 + c/n^a *)
		If[Length[t]<=2, Print["Not enough terms to compute s[i]"]; Break[]];
		
		m = Exponent[t, z, Max] - Exponent[t, z, Min];
		sls = Append[sls, Normal[ Series[ t * (t /.z->(z^rho+2)^(1/rho))
			/(1-1/(sls[[i-1]]/.z->(z^rho+1)^(1/rho)))^2, {z, Infinity, m}] ] ];
	];
	
	Return[sls];
]






(*
######################
Given asymptotici expression of s[i-1] and bounds lb, ub 
compute bounds f and g of s[i-1] to ensure lb <= s[i] <= ub
######################
*)
SBoundFind[s_, z_, rho_, lb_, ub_] := Module[
	{m, p, t, f,g, re},
	
	(* we require the minimal power of f and g is at most the same as lb and ub *)
	m = Min[Exponent[lb, z, Min], Exponent[s-1, z, Max]-1];
	
	
	(* starting from the minimal power to find f and g *)
	For[p=m, p>=Exponent[s, z, Min], p--,
		t = Normal[Series[s, {z, Infinity, -p}]];
		f = t - z^p;
		g = t + z^p;
		
		re = IsPos[ (f-1)*(SubsLow[f,z,rho,2]-1)/(1-1/SubsUpp[g,z,rho,1])^2 - lb, z, rho];
		If[re[[1]], N0=re[[2]], Continue[]];
		re = IsPos[ ub - (g-1)*(SubsUpp[g,z,rho,2]-1)/(1-1/SubsLow[f,z,rho,1])^2 , z, rho];
		If[re[[1]], N0=Max[N0, re[[2]]]; Return[{True, f, g, N0}]];
	];
	
	Return[{False, 0}];
]
		
	
(*
######################
Given asymptotic expression of r(n)=a_{n+1}/a_n and bounds lb, ub 
compute bounds f and g of r(n) to ensure lb <= s[1]=r(n+1)/r(n) <= ub
######################
*)
RBoundFind[r_, z_, rho_, lb_, ub_] := Module[
	{p, t, f,g, re},
	
	(* starting from the minimal power to find f and g *)
	For[p=Exponent[r, z, Max]-1, p>=Exponent[r, z, Min], p--,
		t = Normal[Series[r, {z, Infinity, -p}]];
		f = t - z^p;
		g = t + z^p;
		
		re = IsPos[ SubsLow[f,z,rho,1]/g - lb, z, rho];
		If[re[[1]], N0=re[[2]], Continue[]];
		re = IsPos[ ub - SubsUpp[g,z,rho,1]/f , z, rho];
		If[re[[1]], N0=Max[N0, re[[2]]]; Return[{True, f, g, N0}]];
	];
	
	Return[{False, 0}];
]

(*
######################
Given asymptotic expression of r(n)=a_{n+1}/a_n and bounds lb, ub 
compute bounds f and g of r(n) to ensure lb <= s[1]=r(n)/r(n-1) <= ub
######################
*)
RBoundFind1[r_, z_, rho_, lb_, ub_] := Module[
	{p, t, f,g, re},
	
	(* starting from the minimal power to find f and g *)
	For[p=Exponent[r, z, Max]-1, p>=Exponent[r, z, Min], p--,
		t = Normal[Series[r, {z, Infinity, -p}]];
		f = t - z^p;
		g = t + z^p;
		
		re = IsPos[ SubsLow[f,z,rho,1]/g - (lb/.z -> (z^rho + 1)^(1/rho)), z, rho];
		If[re[[1]], N0=re[[2]], Continue[]];
		re = IsPos[ (ub /. z -> (z^rho + 1)^(1/rho)) - SubsUpp[g,z,rho,1]/f , z, rho];
		If[re[[1]], N0=Max[N0, re[[2]]]; Return[{True, f, g, N0}]];
	];
	
	Return[{False, 0}];
]





(*
######################
Check if the sequence is good 
######################
*)

IsBP[L_, n_, N_, r_] := Module[
	{rls, t, i, tmp, s},
	
	rls = L2R[L,n,N]; t = Length[rls];
	s = 0;
	
	For[i=0, i<t-1, i++,
		
		If[IsPos[rls[[i+1]], n, 1][[1]], tmp = rls[[i+1]], 
			tmp = -rls[[i+1]]];
			
		s = s + tmp/Product[r/.n->n+j, {j,i,t-2}]
					*Sum[1/(r/.n->n+j), {j,i,t-2}];
		];
		
	tmp = Limit[s, n->Infinity];
	
	Return[{If[tmp<1, True, False], tmp}];
	
]





(*
######################
Transform a general annihilator to a starndard annihilator of form
a_0 + a_1 N + ... a_t N^t with a_0,a_t \not= 0
######################
*)

NormL[L_, n_, N_] := Module[
	{ldeg, ls},
	
  	ldeg = Exponent[L, N, Min];
  	ls = Exponent[L, N, List];
  	
  	Return[Total[ Map[
    	Factor[(Coefficient[L, N, #] /. n -> n - ldeg)] N^(# - ldeg) &,  ls]]];
]




(*
######################
Given an annihilator L of a_n, compute the list {R_i} such that
a_{n+r} = R_0 a_n + R_1 a_{n+1} + ... + R_{t-1} a_{n+t-1}
######################
*)

L2R[L_, n_, N_] :=Module[
	{newL, deg},
	
	newL=NormL[L, n, N];
	deg=Exponent[newL, N];
	
	Return[Map[-Coefficient[newL, N, #]/Coefficient[newL, N, deg] &, Range[0,deg-1]]];
]



(*
######################
Compute the whether or not a rational function r(z) is positive
for z >= b^(1/rho)
######################
*)

IsPos[r_, z_, rho_] :=Module[
	{t, nu, de, rat, res, b},
	
	t = Together[r];
	nu = Numerator[t]; de = Denominator[t];
	
	rat=Coefficient[nu, z, Exponent[nu, z]]/Coefficient[de, z, Exponent[de, z]];
	res=If[rat>0, True, False];
	
	b = Floor[ Max[-1, 
		Map[z /. # &, N[Solve[nu == 0, z, Reals]]], 
    	Map[z /. # &, N[Solve[de == 0, z, Reals]]]]] + 1;
    	
    b = b^rho;
    
    For[NULL, b>0, b--,
    	If[(de/.z->(b-1)^(1/rho)) == 0 || N[(t/.z->(b-1)^(1/rho))] < 0, Break[]];
    	];
    	
	Return[{res, b}];
]





(*
######################
Give an upper bound of the substitution n->n+i by the inequality
(n+i)^a >= n^a (1+a i/n + a(a-1)/2 i^2/n^2) for 0<a<1 
Input: a polynomial in z=n^(1/rho)
Output: a polynomial in z
######################
*)

SubsUpp[pol_, z_, rho_, i_] := Module[
	{pls,s,j, p,c,intp,ratp},
	
	pls = Exponent[pol, z, List];
	s = 0;
	
	For[j=1, j<=Length[pls], j++,
		p=pls[[j]]; c=Coefficient[pol, z, p];
		
		If[c>0,
		
			intp = Ceiling[p/rho]; ratp = p-rho*intp; (* (n+i)^(-3/2) <= (n+i)^(-1) n^(-1/2) *)
			s = s + c * (z^rho+i)^intp * z^ratp*(1 + ratp/rho*i/z^rho + (ratp/rho)*(ratp/rho-1)/2*i^2/z^(2*rho)),   
			
			intp = Floor[p/rho]; ratp = p-rho*intp; (* (n+i)^(-3/2) >= (n+i)^(-2) n^(1/2) *)
			s = s + c * (z^rho+i)^intp * z^ratp*(1 + ratp/rho*i/z^rho + (ratp/rho)*(ratp/rho-1)/2*i^2/z^(2*rho)); 
		];
	];
	
	Return[s];
]
		
		


(*
######################
Give an lower bound of the substitution n->n+i by the inequality
n^a <= (n+i)^a 
Input: a polynomial in z=n^(1/rho)
Output: a polynomial in z
######################
*)

SubsLow[pol_, z_, rho_, i_] := Module[
	{pls,s,j, p,c, intp,ratp},
	
	pls = Exponent[pol, z, List];
	s = 0;
	
	For[j=1, j<=Length[pls], j++,
		p=pls[[j]]; c=Coefficient[pol, z, p];
		
		If[c>0,
		
			intp = Floor[p/rho]; ratp = p-rho*intp;
			s = s + c * (z^rho+i)^intp * z^ratp*(1 + ratp/rho*i/z^rho + (ratp/rho)*(ratp/rho-1)/2*i^2/z^(2*rho)),  
			
			intp = Ceiling[p/rho]; ratp = p-rho*intp; 
			s = s + c * (z^rho+i)^intp * z^ratp*(1 + ratp/rho*i/z^rho + (ratp/rho)*(ratp/rho-1)/2*i^2/z^(2*rho));
		];
	];
	
	Return[s];
]
		
		


(*
######################
Given lower bound f(n) and upper bound g(n), test if the bounds are kept by the recurrence relation. More precisely, 
R_0/(u0(n) u0(n+1) ... u0(n+t-1)) + R_1/(u1(n+1) ... u1(n+t-1)) + ... + R_{t-1} - f(n+t-1) >= 0
g(n+t-1) - R_0/(v0(n) v0(n+1) ... v0(n+t-1)) + R_1/(v1(n+1) ... v1(n+t-1)) + ... + R_{t-1}  >= 0
######################
*)

TestR[L_, n_, N_, f_, g_, z_, rho_, comput_:True] :=Module[
	{Rls, len, s1,s2, t, N, i,j},
	
	Rls=L2R[L, n, N]; 
	
	len=Length[Rls];
	s1 = -SubsUpp[f, z, rho, len-1];
	s2 = SubsLow[g, z, rho, len-1];
	
	
	t = Map[IsPos[#, n, 1] &, Rls]; 
	If[rho>1, N0=1, N0=0];
	
	For[i=1, i<=len, i++,
		If[N0<t[[i]][[2]], N0=t[[i]][[2]]];
		If[t[[i]][[1]], 
			s1=s1+(Rls[[i]] /. n->z^rho)/Product[SubsUpp[g, z, rho, j], {j,i-1,len-2}];
			s2=s2-(Rls[[i]] /. n->z^rho)/Product[SubsLow[f, z, rho, j], {j,i-1,len-2}],
			s1=s1+(Rls[[i]] /. n->z^rho)/Product[SubsLow[f, z, rho, j], {j,i-1,len-2}];
			s2=s2-(Rls[[i]] /. n->z^rho)/Product[SubsUpp[g, z, rho, j], {j,i-1,len-2}]];
		];
	
	If[Not[comput], Return[{s1,s2}]];
	
	t = IsPos[s1, z, rho]; 
	
	If[t[[1]], N0=Max[{N0, t[[2]]}], Print[1, ", ", s1]; Return[{False, 1}]];
	
	t = IsPos[s2, z, rho];
	If[t[[1]], N0=Max[{N0, t[[2]]}], Print[2, ", ", s2]; Return[{False, 1}]]; 
	
	Return[{True, N0}];
]


(*
######################
Compute the bounds of a_{n+1}/a_n
######################
*)

RootLog[L_, n_, N_, inival_, K_] := Module[
	{t, rho, an, z, rat, deg, s, N0, lb, ub, fn, gn, a, hn, h, k, j},
	
	t = Asy[L, n, N, K];
	rho = t[[1]][[2]];
	an = t[[1]][[3]][[1]];
	
	(* compute the asymptotic expression of s[1] *)
	
	rat = Series[(an /.n -> z^rho + 1)/(an /.n->z^rho), {z, Infinity, 0}];
	deg = Exponent[rat, z, Max];
	rat = Normal[Series[(an /.n -> z^rho + 1)/(an /.n->z^rho), {z, Infinity, K - deg - 1}]];
	
	t = IsBP[L, n, N, (rat/.z->n^(1/rho))];
	If[Not[t[[1]]], Print["Not a bound preserving sequence: limit = ", t[[2]]]; Return[{False, 0}]];
		
	deg = Exponent[rat, z, Max] - Exponent[rat, z, Min];
	s = Normal[Series[(rat /.z -> (z^rho + 1)^(1/rho))/rat, {z, Infinity, deg}]];
	
	(* compute the bounds for a_n+1/a_n *)
	
	N0 = 0;
    lb = Normal[Series[s, {z, Infinity, deg-1}]] - 1/z^(deg-1);
	ub = Normal[Series[s, {z, Infinity, deg-1}]] + 1/z^(deg-1);
	t = RBoundFind[rat, z, rho, lb, ub];
	If[t[[1]], lb = t[[2]]; ub = t[[3]]; N0 = Max[N0, t[[4]]]; Print[(lb/.z->n^(1/rho)),"<=a_{n+1}/a_n<=",(ub/.z->n^(1/rho))," for n>=", t[[4]]], Return[{False, 0}]];
	
	t = TestR[L, n, N, lb, ub, z, rho];
	If[t[[1]], N0 = Max[N0, t[[2]]]; Print["a_n preserves the bounds for n>= ", t[[2]]]];
		
	j = FindR[L, n, N, inival, lb, ub, z, rho];
	Print["the bounds hold for n>= ", j];
	
	Return[{{lb,ub}/.z->n^(1/rho), Max[N0, j]}];

]
