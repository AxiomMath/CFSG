module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Omega
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmIso

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega MulAction

abbrev GL6 := F6 ≃ₗ[ZMod 2] F6

noncomputable abbrev O6 : Subgroup GL6 := TauCeti.QuadraticMap.orthogonalGroup qMinusForm

@[expose] def mkLE (f g : F6 → F6) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsm : ∀ (c : ZMod 2) (x : F6), f (c • x) = c • f x) (h1 : ∀ x, g (f x) = x)
    (h2 : ∀ x, f (g x) = x) : GL6 where
  toFun := f
  invFun := g
  map_add' := hadd
  map_smul' := hsm
  left_inv := h1
  right_inv := h2

theorem mkLE_mem_O6 {f g : F6 → F6} {hadd hsm h1 h2} (h : ∀ x, qMinus (f x) = qMinus x) :
    mkLE f g hadd hsm h1 h2 ∈ O6 := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [qMinusForm_apply, qMinusForm_apply]
  exact h v

@[expose] def fa1 (v : F6) : F6 := ![v 1 + v 3, v 0 + v 3, v 3, v 0 + v 1 + v 2 + v 3, v 4, v 5]
@[expose] def fa2 (v : F6) : F6 := ![v 1, v 0 + v 1 + v 2 + v 3, v 1 + v 3, v 1 + v 2, v 4, v 5]
@[expose] def fa3 (v : F6) : F6 := ![v 0, v 1, v 2, v 3, v 5, v 4 + v 5]
@[expose] def fs1 (v : F6) : F6 := ![v 1 + v 2, v 0 + v 2, v 2, v 0 + v 1 + v 2 + v 3, v 4, v 5]
@[expose] def fs2 (v : F6) : F6 := ![v 1, v 0, v 2, v 3, v 4, v 5]
@[expose] def fs3 (v : F6) : F6 := ![v 0, v 1, v 2, v 3, v 5, v 4]
@[expose] def fsg (v : F6) : F6 :=
  ![v 1 + v 2 + v 3 + v 4, v 1 + v 2 + v 3 + v 5, v 0 + v 1 + v 4 + v 5,
    v 0 + v 2 + v 3 + v 4 + v 5, v 0 + v 1 + v 3, v 2 + v 3]
@[expose] def ftu (v : F6) : F6 :=
  ![v 2 + v 3 + v 4, v 2 + v 3 + v 5, v 0 + v 1 + v 2 + v 4 + v 5, v 0 + v 1 + v 3 + v 4 + v 5,
    v 0 + v 2 + v 3, v 1 + v 2 + v 3]

theorem fa1_add : ∀ x y, fa1 (x + y) = fa1 x + fa1 y := by decide +kernel
theorem fa2_add : ∀ x y, fa2 (x + y) = fa2 x + fa2 y := by decide +kernel
theorem fa3_add : ∀ x y, fa3 (x + y) = fa3 x + fa3 y := by decide +kernel
theorem fs1_add : ∀ x y, fs1 (x + y) = fs1 x + fs1 y := by decide +kernel
theorem fs2_add : ∀ x y, fs2 (x + y) = fs2 x + fs2 y := by decide +kernel
theorem fs3_add : ∀ x y, fs3 (x + y) = fs3 x + fs3 y := by decide +kernel
theorem fsg_add : ∀ x y, fsg (x + y) = fsg x + fsg y := by decide +kernel
theorem ftu_add : ∀ x y, ftu (x + y) = ftu x + ftu y := by decide +kernel

theorem fa1_smul : ∀ (c : ZMod 2) x, fa1 (c • x) = c • fa1 x := by decide +kernel
theorem fa2_smul : ∀ (c : ZMod 2) x, fa2 (c • x) = c • fa2 x := by decide +kernel
theorem fa3_smul : ∀ (c : ZMod 2) x, fa3 (c • x) = c • fa3 x := by decide +kernel
theorem fs1_smul : ∀ (c : ZMod 2) x, fs1 (c • x) = c • fs1 x := by decide +kernel
theorem fs2_smul : ∀ (c : ZMod 2) x, fs2 (c • x) = c • fs2 x := by decide +kernel
theorem fs3_smul : ∀ (c : ZMod 2) x, fs3 (c • x) = c • fs3 x := by decide +kernel
theorem fsg_smul : ∀ (c : ZMod 2) x, fsg (c • x) = c • fsg x := by decide +kernel
theorem ftu_smul : ∀ (c : ZMod 2) x, ftu (c • x) = c • ftu x := by decide +kernel

theorem fa1_cube : ∀ x, fa1 (fa1 (fa1 x)) = x := by decide +kernel
theorem fa2_cube : ∀ x, fa2 (fa2 (fa2 x)) = x := by decide +kernel
theorem fa3_cube : ∀ x, fa3 (fa3 (fa3 x)) = x := by decide +kernel
theorem fsg_cube : ∀ x, fsg (fsg (fsg x)) = x := by decide +kernel
theorem fs1_sq : ∀ x, fs1 (fs1 x) = x := by decide +kernel
theorem fs2_sq : ∀ x, fs2 (fs2 x) = x := by decide +kernel
theorem fs3_sq : ∀ x, fs3 (fs3 x) = x := by decide +kernel
theorem ftu_sq : ∀ x, ftu (ftu x) = x := by decide +kernel

@[expose] def a1 : GL6 := mkLE fa1 (fun v => fa1 (fa1 v)) fa1_add fa1_smul fa1_cube fa1_cube
@[expose] def a2 : GL6 := mkLE fa2 (fun v => fa2 (fa2 v)) fa2_add fa2_smul fa2_cube fa2_cube
@[expose] def a3 : GL6 := mkLE fa3 (fun v => fa3 (fa3 v)) fa3_add fa3_smul fa3_cube fa3_cube
@[expose] def s1 : GL6 := mkLE fs1 fs1 fs1_add fs1_smul fs1_sq fs1_sq
@[expose] def s2 : GL6 := mkLE fs2 fs2 fs2_add fs2_smul fs2_sq fs2_sq
@[expose] def s3 : GL6 := mkLE fs3 fs3 fs3_add fs3_smul fs3_sq fs3_sq
@[expose] def sg : GL6 := mkLE fsg (fun v => fsg (fsg v)) fsg_add fsg_smul fsg_cube fsg_cube
@[expose] def tu : GL6 := mkLE ftu ftu ftu_add ftu_smul ftu_sq ftu_sq

theorem fa1_q : ∀ x, qMinus (fa1 x) = qMinus x := by decide +kernel
theorem fa2_q : ∀ x, qMinus (fa2 x) = qMinus x := by decide +kernel
theorem fa3_q : ∀ x, qMinus (fa3 x) = qMinus x := by decide +kernel
theorem fs1_q : ∀ x, qMinus (fs1 x) = qMinus x := by decide +kernel
theorem fs2_q : ∀ x, qMinus (fs2 x) = qMinus x := by decide +kernel
theorem fs3_q : ∀ x, qMinus (fs3 x) = qMinus x := by decide +kernel
theorem fsg_q : ∀ x, qMinus (fsg x) = qMinus x := by decide +kernel
theorem ftu_q : ∀ x, qMinus (ftu x) = qMinus x := by decide +kernel

theorem a1_mem : a1 ∈ O6 := mkLE_mem_O6 fa1_q
theorem a2_mem : a2 ∈ O6 := mkLE_mem_O6 fa2_q
theorem a3_mem : a3 ∈ O6 := mkLE_mem_O6 fa3_q
theorem s1_mem : s1 ∈ O6 := mkLE_mem_O6 fs1_q
theorem s2_mem : s2 ∈ O6 := mkLE_mem_O6 fs2_q
theorem s3_mem : s3 ∈ O6 := mkLE_mem_O6 fs3_q
theorem sg_mem : sg ∈ O6 := mkLE_mem_O6 fsg_q
theorem tu_mem : tu ∈ O6 := mkLE_mem_O6 ftu_q

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
