module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Check

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.Quasithin.G2U

@[expose] def uIdx : Std.HashMap (List ℕ) ℕ := indexMap uElems

@[expose] def posOf (c : List ℕ) : ℕ := if found uElems uIdx c then (uIdx.get? c).getD 729 else 729

@[expose] def uKindArr : Array ℕ := uKind.toArray

@[expose] def kindAt (p : ℕ) : ℕ := uKindArr.getD p 0

@[expose] def uRtArr : Array Bool :=
  (List.range 729).toArray.map fun p => uRt.contains p

@[expose] def inRt (p : ℕ) : Bool := uRtArr.getD p false

@[expose] def rtProd (e : ℕ) : List ℕ :=
  mul4 (mul4 (mul4 (pow4 (uAt (uLiftBasis.getD 0 0)) (e % 3))
    (pow4 (uAt (uLiftBasis.getD 1 0)) (e / 3 % 3)))
    (pow4 (uAt (uLiftBasis.getD 2 0)) (e / 9 % 3)))
    (pow4 (uAt (uLiftBasis.getD 3 0)) (e / 27 % 3))

@[noinline, expose] def uRtCheck : Bool :=
  uLiftBasis.length == 4 && uLiftBasis.all (· < 729) &&
    (List.range 4).all (fun a => (List.range 4).all fun b =>
      commutes4 (uAt (uLiftBasis.getD a 0)) (uAt (uLiftBasis.getD b 0))) &&
    (List.range 4).all (fun a => cube4 (uAt (uLiftBasis.getD a 0)) == one4) &&
    uRt.length == 81 && uRt.all (· < 729) &&
    (List.range 81).all (fun e => uRt.contains (posOf (rtProd e))) &&
    distinctCheck ((List.range 81).map rtProd).toArray

@[expose] def convRWord (p : ℕ) : List ℕ := (uConvR.lookup p).getD []

@[expose] def convDWord (p : ℕ) : List ℕ := (uConvD.lookup p).getD []

@[expose] def kindOK (p : ℕ) : Bool :=
  uKind.getD p 0 != 3 ||
    (wordOK (convDWord p) && conjStep (wordPair (convDWord p)) (uAt p) == uAt uB0)

@[noinline, expose] def uKindCheck : Bool :=
  uKind.length == 729 && uB0 < 729 && (List.range 729).all kindOK &&
    uConvR.all fun e => wordOK e.2

@[noinline, expose] def uZCheck : Bool :=
  uZ < 729 && !(uAt uZ == one4) && cube4 (uAt uZ) == one4 &&
    (List.range 729).all fun q => commutes4 (uAt q) (uAt uZ)

@[noinline, expose] def uCentCheck : Bool :=
  cube4 (uAt uB0) == one4 &&
    ((List.range 729).filter fun q => commutes4 (uAt q) (uAt uB0)).length == 81

@[expose] def orbGens : List (List ℕ) := [wordPair [0], wordPair [1]]

@[expose] def orbitBuild (x₀ : List ℕ) (gens : List (List ℕ)) (par : List (ℕ × ℕ)) :
    Array (List ℕ) :=
  par.foldl (fun acc ps =>
    acc.push (conjStep (gens.getD ps.2 (wordPair [])) (acc.getD ps.1 x₀))) #[x₀]

@[expose] def uOrbit : Array (List ℕ) :=
  orbitBuild (uAt uB0) orbGens
    (bfsParents (uAt uB0) (fun x p => conjStep p x) orbGens 40320)

set_option compiler.extract_closed false in
@[noinline, expose] def uOrbitCheck : Bool :=
  uOrbit.size == 40320 && distinctCheck uOrbit

set_option compiler.extract_closed false in
@[noinline, expose] def uClassCheck : Bool :=
  uRtCheck && uKindCheck && uCentCheck && uOrbitCheck && uZCheck

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
