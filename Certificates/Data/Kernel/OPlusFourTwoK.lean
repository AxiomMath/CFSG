module

public import Certificates.Data.OPlusFourTwo

public section

namespace CFSG.KC.OPlusFourTwo

open CFSG.OPlusFourTwo

abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def vecs : List (Fin 4 → ZMod 2) :=
  [![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0],
   ![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0],
   ![0, 0, 0, 1], ![1, 0, 0, 1], ![0, 1, 0, 1], ![1, 1, 0, 1],
   ![0, 0, 1, 1], ![1, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1]]

@[expose] def mulE (M N : Mat) : Mat :=
  Matrix.of fun i j => M i 0 * N 0 j + M i 1 * N 1 j + M i 2 * N 2 j + M i 3 * N 3 j

@[expose] def mulVecE (M : Mat) (v : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  fun i => M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 + M i 3 * v 3

@[expose] def eqE (M N : Mat) : Bool :=
  decide (M 0 0 = N 0 0 ∧ M 0 1 = N 0 1 ∧ M 0 2 = N 0 2 ∧ M 0 3 = N 0 3 ∧
    M 1 0 = N 1 0 ∧ M 1 1 = N 1 1 ∧ M 1 2 = N 1 2 ∧ M 1 3 = N 1 3 ∧
    M 2 0 = N 2 0 ∧ M 2 1 = N 2 1 ∧ M 2 2 = N 2 2 ∧ M 2 3 = N 2 3 ∧
    M 3 0 = N 3 0 ∧ M 3 1 = N 3 1 ∧ M 3 2 = N 3 2 ∧ M 3 3 = N 3 3)

@[expose] def cubeE (M : Mat) : Mat := mulE (mulE M M) M

@[expose] def pow12E (M : Mat) : Mat :=
  let C := cubeE M
  let S := mulE C C
  mulE S S

@[expose] def ofCols (c0 c1 c2 c3 : Fin 4 → ZMod 2) : Mat :=
  Matrix.of fun i j => ![c0, c1, c2, c3] j i

@[expose] def treeB (L : List Mat) : Bool :=
  vecs.all fun c0 => !(decide (q0 c0 = 0)) || vecs.all fun c1 =>
    !(decide (q0 c1 = 0 ∧ q0 (c0 + c1) = 1)) || vecs.all fun c2 =>
      !(decide (q0 c2 = 0 ∧ q0 (c0 + c2) = 0 ∧ q0 (c1 + c2) = 0)) || vecs.all fun c3 =>
        !(decide (q0 c3 = 0 ∧ q0 (c0 + c3) = 0 ∧ q0 (c1 + c3) = 0 ∧ q0 (c2 + c3) = 1)) ||
          L.any (eqE (ofCols c0 c1 c2 c3))

@[expose] def soundB (L : List Mat) : Bool :=
  L.all fun M => vecs.all fun v => decide (q0 (mulVecE M v) = q0 v)

abbrev DistinctP (L : List Mat) : Prop :=
  L.Pairwise fun M N => eqE M N = false

@[expose] def pow12B (L : List Mat) : Bool :=
  L.all fun M => eqE (pow12E M) 1

end CFSG.KC.OPlusFourTwo
