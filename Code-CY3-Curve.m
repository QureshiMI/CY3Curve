///////////////////////////////
// This code is for the computation of candidate CY 3-folds with C=1/2(1,1) curve
// in P^n(w_i) that can be complete intersections in weighted projective space with sum of the weights equal to W and canonical class kx
///////////////////////////////////////

// These are basic functions for the computation of the candidate CY 3-folds. 
Q:=Rationals();
R<t>:=PolynomialRing(Q);
K:=FieldOfFractions(R);
S<s>:=PowerSeriesRing(Q,50);

//////////////////////////////////
//To compute the contribution of Hilbert series by an orbifold point 1/r(a,b,c) singularity. 
function Qorb(r,LL,k)
L := [Integers() | i : i in LL];
if (k + &+L) mod r ne 0
then error "Error: Canonical weight not compatible";
end if;
n := #L; Pi := &* [ 1 - t^i : i in L ];
A := (1-t^r) div (1-t); B := Pi div (1-t)^n;
H := GCD(A, B); M := &* [GCD(A, 1-t^i) : i in L];
shift := Floor(Degree(M*H)/2);
l := Floor((k+n+1)/2+shift+1);
de := Maximum(0,Ceiling(-l/r));
m := l + de*r;
G, al_throwaway, be := XGCD(A div H, t^m*B div M);
return t^m*be/(M*(1-t)^n*(1-t^r)*t^(de*r));
end function;
// This computes the initial term of the Hilbert series of a complete intersection in P^n(w_i) with sum of the weights equal to W and canonical class kx
function Init_Term(hs,c,n)
if c lt 0 then pini:=0;
else if c eq 0 then pini:=1/(1 - t)^(n + 1);
else
cs:=Coefficients(S ! hs)[1..Floor(c/2) + 1];
pp:=&+[cs[i] * t^(i - 1) : i in [1..#cs]] * (1 - t)^(n + 1);
	if IsEven(c) eq true then
	pini:=(&+[Coefficient(pp, i )*(t^i+t^(c-i)):i in [0..c div 2-1]]+
	Coefficient(pp,c div 2)*t^(Floor(c/2)))/(1 - t)^(n + 1);
	else
 	pini:= &+[Coefficient(pp,i)*(t^i+t^(c-i)):i in [0..Floor(c/2)]]/(1 - t)^(n + 1);
	end if;
end if; end if;
return pini;
end function;



// This calculates all 3- fold complete intersections of codimens c with canonical class kx with sum of the weights W.
procedure Format_CI_CY3(W, c)
    n:=3;
    s :=  c + 4; // embedding in P^{s-1}
    Sum_Weights := W; // Sum of the weights on P^{s-1}
    Eq_Degs := [Sort(p): p in Partitions(W, c)]; // The list of equation degrees  sum of weights W 
    for eq_deg in Eq_Degs do
        // Avoid intersections with a linear cone
        Poss_Embeddings := [Sort(p): p in Partitions(Sum_Weights, s) | #(Seqset(p) meet Seqset(eq_deg)) eq 0];

        if #Poss_Embeddings gt 0 then 
            for weight in Poss_Embeddings do
            X := weight cat eq_deg;
            num := &*[1 - t^a : a in eq_deg];
            den := &*[1 - t^a : a in weight];// eq_deg is list of complete intersection in P[weights]
            px  := num / den;
            deg := Evaluate(px * (1 - t)^(n + 1), 1);
            pini := Init_Term(px, n +  1, n);//Initial term

            if px eq pini then // this checks if X is smooth. 
                ok := px;
            else
                Porb_c := Qorb(2, [1,1], 2) / (1 - t^2);//curve contribution
                Porb := [Porb_c];
                R := [2];
                B := [1,1 ];
                den := &*[Denominator(PQ) : PQ in Porb] * Denominator(px) * Denominator(pini);
                PX := den * px;
                Pini := den * pini;
                Porb := [PQ * den : PQ in Porb];
                LHS := PX - Pini;
                V := Vector(Integers(), [Evaluate(LHS, k) : k in [2..#R + 1]]);
                A := Matrix([PowerSequence(Integers()) | [Evaluate(PQ, k) : k in [2..#R + 1]] : PQ in Porb ]);
                ok, sol := IsConsistent(A, V);

                    if ok and Min(Eltseq(sol)) ge 0 and (LHS - &+[sol[m] * Porb[m] : m in [1..#R]] eq 0) 
                    then
                        printf "\nCandidate CY 3-fold with C= 1/2(1,1) curve\n" 
                            cat "Ambient: P%o\n" 
                            cat "Eq Degs: %o\n"
                            cat "DegreeD_C: %o\n" 
                            cat "Degree:%o\n",
                            weight, eq_deg, sol[1]/2, deg;
                            "\n------------------------------";
                    end if;
            end if;
            end for;    
        end if;
    end for;
end procedure;

for q in [1..15] do
Format_CI_CY3(q,1);
"\n===========================================",q;
end for;