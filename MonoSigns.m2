newPackage(
	"MonoSigns",
	Version => "0.1",
	Date => "March 2020",
	Authors => {{
		  Name => "Alexandru Iosif",
		  Email => "iosif@aices.rwth-aachen.de",
		  HomePage => "https://alexandru-iosif.github.io"}},
    	Headline => "A package for reducing polynomial systems of
    equations with nonnegative solutions",
	AuxiliaryFiles => false,    
    	PackageImports => {"Elimination"},
	DebuggingMode => true --set to false once the package is in finished form
)

export {
     -- 'Official' functions
     "reducedRowEchelon",
     "monoSignsRows",
     "reduceSystemOnce"

     -- Not in the interface:
     
     --Not yet built:
     --upperLowerTriangular,
     --reduceSystemFull
}

reducedRowEchelon = A ->(
    --this function returns the row echelon form of a matrix it is
    --taken from the Macaulay2 package Binomials of Thomas Kahle (that
    --A. Iosif jointed in 2018)
    --NB: here entries of the output live in
    --the fraction field of the entries of the input. This should
    --eventually become an option in te interface
    if A == 0 then return A;
    c := numColumns A;
    variable := symbol variable;
    R:=frac(ring (A_(0,0))); S := R[variable_1..variable_c,MonomialOrder => Lex];
    A=sub(transpose(coefficients(matrix {flatten entries gens gb ideal flatten entries (sub(A,S)*transpose(vars S))},
		Monomials=> flatten entries vars S))_1,R);
    matrix reverse entries A)

-- upperLowerTriangular = A->(
--     --this is a function which converts a matrix into its upper-lower triangular form:
--     --I think that, this form should be the one that contains the largest number of non-negative rows
--     )

monoSignsRows = A ->(
    cRow := symbol cRow;
    bcRow := symbol bcRow;
    nN := {};
    R := RR;
    AR := substitute (A,R);
    for i from 0 to numrows AR - 1 do(
    	cRow = toList set flatten entries AR^{i};
    	cRow = cRow - set{0_R};
    	bcRow = set apply(cRow, j -> j < 0);
	if toList bcRow == {false} or toList bcRow == {true} then( 
	    nN = nN | {flatten entries A^{i}};
	    );
	);
    if nN == {} then nN = {{}};
    matrix nN
    )

-- findNonNegative = A ->(
--     --This function takes a Matrix and tries to find a linear
--     --combination of its row that is nonnegative.
--     )

reduceSystemOnce = (A,R) ->(
    --R should not contain the parameters as variables. Instead use R
    --= K[variables], where K = frac(QQ[parameters]).
    --
    --This function takes as an input a one column
    --matrix A whose rows are polynomials in R.  Then it supposes that
    --the solutions of this system and the eventual parameters from
    --the coefficient field of R are positive and nonnegative,
    --respectively. It tries to find linear combinations of these
    --polynomials which are either nonnegative or nonpositive. Then,
    --if the parameters are positive and the solution are nonnegative,
    --then each monomial from such a sum has tu be zero. The primary
    --decomposition of the resulting monomial ideal will give branches
    --in which some variables are zero.  This function performs this
    --reduction once. The output is a list {(A_i,R_i)}, where A_i
    --represents a matrix with the new system that lives in the
    --reduced ring R_i (that this R - variables that are zero on this
    --branch).

    K := coefficientRing R;
    variablesR := vars R;
    A = sub(A,R);
    (M,C) := coefficients A;
    M = transpose M;
    C = reducedRowEchelon transpose C; -- make it an option to first compute the reducedRowEchelon
    nonNegativeC := sub(monoSignsRows C, R);
    zeroMonomials := monomials (nonNegativeC*M);
    zeroVariableIdeals := associatedPrimes sub(ideal flatten entries zeroMonomials,QQ[flatten entries variablesR]);
    L := {};
    zeroVariables := symbol zeroVariables;
    RI := symbol RI;
    nonZeroVariables := symbol nonZeroVariables;
    newA := symbol newA;
    newSystem := symbol newSystem;
    for I in zeroVariableIdeals do(
    	use R;
    	zeroVariables = set flatten entries sub(gens I,R);
    	nonZeroVariables = toList(set flatten entries variablesR - zeroVariables);
    	RI = K[nonZeroVariables];
    	newSystem = sub(A,RI);
    	newSystem = set flatten entries newSystem - set {0_RI};
    	newSystem = matrix{toList newSystem};
	newSystem = sub(newSystem,R);
	nonZeroVariables = sub(matrix{nonZeroVariables},R);
	zeroVariables = sub(matrix{toList zeroVariables},R);
    	L = L|{{newSystem,nonZeroVariables,zeroVariables}};
    	);
    L)


-- reduceSystemFull = (A,R) ->(
--     -- This does the same as reduceSystemOnce recursively, until no
--     -- change is detected.
    
--     -- I need to think how to implement this. It needs to be done in a
--     -- tree way: Imagine that I have an output of reduceSystemOnce,
--     -- that is a list. For each element of this list I want to apply
--     -- the function reduceSystemOnce again, and repeat the
--     -- process. This leads me to branches. Some paths might finish
--     -- earlier than others, so I want to stop computations on those
--     -- paths. Finally, the result of this function should be the final
--     -- points of these paths.
--     L)


beginDocumentation()

document {
    Key => MonoSigns,
    Headline => "a package for reducing polynomial systems of
    equations with nonnegative solutions",    
    EM "MonoSigns", " is a package that takes a polynomial system
    with positive solutions and looks for nonnegative or nonpositive
    polynomials among the equations of the system.",
    }

document {
     Key => {reducedRowEchelon},
     Headline => "the reduced row echelon form of a matrix",
     Usage => "reducedRowEchelon A",
     Inputs => {
          "A" => { "a matrix"} },
     Outputs => {
          {"the reduced row echelon form of A, where zero rows are removed"} },
     EXAMPLE {
          "A = matrix{{1,2},{2,1}}",
          "reducedRowEchelon A",
          },
     Caveat => {"The entries of the output lie in the fraction field of the ring of A. I plan to make this an option."}}

document {
     Key => {monoSignsRows},
     Headline => "the nonnegtive or nonpositive rows of a matrix",
     Usage => "monoSignsRows A",
     Inputs => {
          "A" => { "a matrix"} },
     Outputs => {
          {"the submatrix of A corresponding to the nonnegative or nonpositive rows of A"} },
     EXAMPLE {
          "A = matrix{{1,0},{0,1},{-1,0},{0,-1},{1,-1}}",
          "monoSignsRows A",
          }}


----- TESTS -----
TEST ///--test for reducedRowEchelon
assert (reducedRowEchelon matrix{{1,2},{2,1}} == matrix{{1_QQ,0_QQ},{0_QQ,1_QQ}})
assert (reducedRowEchelon matrix{{1,1,0},{1,2,1}} == matrix{{1_QQ,0_QQ,-1_QQ},{0_QQ,1_QQ,1_QQ}})
///

end
check "MonoSigns"

restart
installPackage "MonoSigns"
viewHelp monoSignsRows

R = QQ[x,y,z];
M = matrix{{x*y+z}};
reduceSystemOnce (M,R)


    
R = QQ[x,y,z,MonomialOrder=>{Weights => {1,0,1}}] -- this gives me the upper-lower triangular form
gens gb ideal(x+y,x+2*y+z)

reducedRowEchelon  matrix{{1,1,0},{1,2,1}}
((submatrix(M,pivotCol))^(-1))*M


