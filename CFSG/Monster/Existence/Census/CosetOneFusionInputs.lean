module

public import CFSG.Monster.B.Rep4371.Interp
public import CFSG.Monster.B.TwoA.Census.CosetEnumBits

public section

namespace CFSG.Monster.Existence.Census

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.AxisCount CFSG.Monster.B.TwoA.Census Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

@[expose] def betaOf : Native.Gen → Model.Pauli → Model.Pauli
  | .sign a => Model.conjYN a
  | .perm arr => Model.conjPermN arr
  | .xi => Model.conjXiN
  | .rho q => Model.conjPauliN q
  | .tau => id

@[expose] def fusF (g : Native.Gen) (c : Model.Pauli) (n : ℕ) : ℕ :=
  Native.CosetEnum.enc (Model.Pauli.mul (betaOf g (pauliDec n)) c)

@[expose] def genMatches : Native.Gen → FusionGenerator → Bool
  | .sign a, r => r.kind == "code_sign" && r.index.any (fun i => a == 2 ^ i)
  | .perm arr, r => (r.kind == "code_permutation" || r.kind == "octad_stabilizer_permutation") &&
      r.permutation == arr.toList
  | .xi, r => r.kind == "xi"
  | _, _ => false

@[expose] def walkEnc (w : List ℕ) (n : ℕ) : ℕ :=
  w.foldl (fun x k => Native.CosetEnum.act (imgs 1) k x) n

@[expose] def fusTarget (j k : ℕ) : ℕ :=
  ((fusionData.generators[j]?).map fun r => r.classTargets.getD k 0).getD 0

@[expose] def fusTree : List (ℕ × ℕ × ℕ) := [
    (0, 0, 1000), (10, 17, 1), (5, 108, 3), (3, 108, 3), (0, 0, 1000), (4, 20, 5), (8, 136, 4),
    (9, 29, 4), (7, 123, 4), (5, 40, 4), (8, 130, 4), (10, 29, 4), (3, 118, 4), (3, 39, 4),
    (2, 95, 4), (5, 125, 4), (9, 114, 3), (0, 0, 0), (0, 1, 2), (10, 20, 5), (8, 40, 4),
    (2, 29, 4), (0, 10, 5), (2, 39, 4), (4, 40, 4), (5, 129, 2), (0, 2, 4), (5, 123, 4),
    (2, 132, 5), (5, 112, 3), (7, 38, 5), (7, 88, 4), (0, 15, 5), (6, 129, 2), (0, 3, 4),
    (6, 123, 4), (3, 116, 4), (3, 29, 4), (9, 40, 4), (6, 112, 3), (1, 112, 3), (5, 105, 2),
    (3, 1, 2), (3, 107, 4), (2, 3, 4), (5, 136, 4), (8, 98, 5), (7, 118, 4), (6, 93, 5),
    (7, 17, 1), (2, 114, 3), (1, 132, 5), (9, 98, 5), (8, 90, 5), (2, 125, 4), (4, 39, 4),
    (9, 82, 4), (4, 89, 3), (5, 130, 4), (8, 88, 4), (1, 116, 4), (5, 16, 4), (2, 85, 5),
    (4, 16, 4), (1, 88, 4), (5, 89, 3), (3, 98, 5), (1, 123, 4), (4, 124, 5), (5, 88, 4),
    (9, 88, 4), (4, 88, 4), (7, 14, 5), (8, 49, 2), (2, 1, 2), (10, 89, 3), (2, 108, 3),
    (9, 55, 5), (3, 123, 4), (6, 116, 4), (2, 116, 4), (4, 17, 1), (3, 114, 3), (7, 132, 5),
    (1, 6, 5), (4, 125, 4), (10, 93, 5), (9, 85, 5), (9, 42, 3), (9, 49, 2), (0, 75, 4),
    (7, 7, 5), (0, 79, 5), (8, 76, 4), (1, 118, 4), (4, 112, 3), (2, 112, 3), (4, 129, 2),
    (0, 76, 4), (4, 123, 4), (9, 44, 5), (6, 118, 4), (4, 10, 5), (0, 95, 4), (10, 88, 4),
    (8, 17, 1), (10, 113, 3), (10, 121, 3), (10, 129, 2), (6, 136, 4), (1, 24, 5), (5, 93, 5),
    (9, 1, 2), (4, 49, 2), (8, 1, 2), (0, 132, 5), (9, 108, 3), (4, 93, 5), (9, 112, 3),
    (9, 39, 4), (3, 95, 4), (9, 129, 2), (0, 107, 4), (8, 112, 3), (0, 116, 4), (8, 108, 3),
    (9, 16, 4), (6, 88, 4), (1, 15, 5), (9, 17, 1), (0, 108, 3), (8, 16, 4), (10, 116, 4),
    (0, 125, 4), (10, 118, 4), (6, 16, 4), (0, 112, 3)
  ]

@[expose] def fusTreeOK : Bool :=
  (List.range 137).all fun k => k == 0 || k == 4 || k == 17 ||
    (let e := fusTree.getD k (0, 0, 0)
     decide (e.1 < 11) && decide (e.2.1 < 137) && (e.2.1 != 0) && (e.2.1 != 4) &&
       decide ((fusTree.getD e.2.1 (0, 0, 0)).2.2 < e.2.2) && fusTarget e.1 k == e.2.1)

end CFSG.Monster.Existence.Census
