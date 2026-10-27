module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchBlock
public import CFSG.LocalAnalysis.StandardType.PhanEMatchKap
public import CFSG.LocalAnalysis.StandardType.PhanEResS2c22x

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

namespace PhanCode

open CFSG.ClassicalInvolution.Phan.PhanE.Flag

@[expose] def plist : PhanCode → List Bool
  | a1moved | a2coll | a3_4c => [false]
  | a2pol | a3_4p => [true]
  | a3_13p => [false, true]
  | _ => []

theorem plist_spec {c : PhanCode} (hc : c.IsFlagCode) :
    ∀ b, b + 1 < c.cut.length → 2 ≤ blockSize c.cut b → c.plist.getD b false = c.polB := by
  intro b hb h2
  cases c <;> simp only [PhanCode.IsFlagCode] at hc
  all_goals
    first
    | exact hc.elim
    | (simp only [PhanCode.cut, List.length_cons, List.length_nil] at hb
       have hb5 : b < 5 := by omega
       interval_cases b <;>
         simp [PhanCode.cut, PhanCode.plist, PhanCode.polB, blockSize] at h2 ⊢)

end PhanCode

namespace Match

open Matrix CFSG.ClassicalInvolution.Phan.PhanE.Flag CFSG.ClassicalInvolution.Phan.PhanE.Res

variable {Fld : Type} [Field Fld] [CharP Fld 2]

theorem coe_permSL_blockPerm_coll {c : PhanCode} (hc : c.IsFlagCode) (hc22 : c ≠ PhanCode.a3_22x)
    (hpol : c.polB = false) :
    ((permSL c.blockPerm : SpecialLinearGroup (Fin (c.rank + 1)) Fld) :
        Matrix (Fin (c.rank + 1)) (Fin (c.rank + 1)) Fld) = 1 := by
  cases c <;> simp only [PhanCode.IsFlagCode] at hc
  all_goals
    first
    | exact hc.elim
    | exact absurd rfl hc22
    | (simp only [PhanCode.polB] at hpol
       exact absurd hpol (by decide))
    | (rw [coe_permSL]
       exact Matrix.permMatrix_one)

theorem coe_permSL_blockPerm_pol {c : PhanCode} (hc : c.IsFlagCode) (hpol : c.polB = true) :
    ((permSL c.blockPerm : SpecialLinearGroup (Fin (c.rank + 1)) Fld) :
        Matrix (Fin (c.rank + 1)) (Fin (c.rank + 1)) Fld) =
      (revBlocks Fld (c.rank + 1) c.cut : Matrix (Fin (c.rank + 1)) (Fin (c.rank + 1)) Fld) := by
  have hd := PhanCode.isCut_cut hc
  have hσ : c.blockPerm = q2cFPt_blockRevI hd := by
    cases c <;> simp only [PhanCode.IsFlagCode] at hc
    case a2pol =>
      ext k
      fin_cases k <;>
        simp only [PhanCode.blockPerm, PhanCode.cut, q2cFPt_blockRevI_apply] <;>
        rw [q2cFPt_blockRev_val_of_block (d := [0, 3]) hd (b := 0)
          (by decide) (by decide) (by decide)] <;>
        decide
    case a3_13p =>
      ext k
      fin_cases k <;>
        simp only [PhanCode.blockPerm, PhanCode.cut, q2cFPt_blockRevI_apply] <;>
        first
        | (rw [q2cFPt_blockRev_val_of_block (d := [0, 1, 4]) hd (b := 0)
              (by decide) (by decide) (by decide)]; decide)
        | (rw [q2cFPt_blockRev_val_of_block (d := [0, 1, 4]) hd (b := 1)
              (by decide) (by decide) (by decide)]; decide)
    case a3_4p =>
      ext k
      fin_cases k <;>
        simp only [PhanCode.blockPerm, PhanCode.cut, q2cFPt_blockRevI_apply] <;>
        rw [q2cFPt_blockRev_val_of_block (d := [0, 4]) hd (b := 0)
          (by decide) (by decide) (by decide)] <;>
        decide
    all_goals
      first
      | exact hc.elim
      | (simp only [PhanCode.polB] at hpol; exact absurd hpol (by decide))
  rw [coe_permSL, hσ]
  simp only [Flag.revBlocks, dif_pos hd]

theorem coe_permSL_blockPerm {c : PhanCode} (hc : c.IsFlagCode) (hc22 : c ≠ PhanCode.a3_22x) :
    ((permSL c.blockPerm : SpecialLinearGroup (Fin (c.rank + 1)) Fld) :
        Matrix (Fin (c.rank + 1)) (Fin (c.rank + 1)) Fld) =
      if c.polB then
        (revBlocks Fld (c.rank + 1) c.cut : Matrix (Fin (c.rank + 1)) (Fin (c.rank + 1)) Fld)
      else 1 := by
  by_cases hpol : c.polB = true
  · rw [if_pos hpol]
    exact coe_permSL_blockPerm_pol hc hpol
  · rw [if_neg hpol]
    exact coe_permSL_blockPerm_coll hc hc22 (by simpa using hpol)

theorem coe_permSL_blockPerm_22x :
    ((permSL PhanCode.a3_22x.blockPerm : SpecialLinearGroup (Fin 4) Fld) :
        Matrix (Fin 4) (Fin 4) Fld) = swap22 Fld := by
  rfl

end Match

end CFSG.ClassicalInvolution.Phan.PhanE

end
