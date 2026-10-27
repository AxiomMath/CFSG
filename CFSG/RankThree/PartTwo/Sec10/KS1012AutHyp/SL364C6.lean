module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL34
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Field

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4.Res6L364 (K64)

theorem exists_det_one_lift {E : Subgroup (MulAut (projectiveSL 3 K64))}
    (hEr : E ≤ (conjAut 3 K64).range) (h4 : 4 ≤ Nat.card E) :
    ∃ A : GL (Fin 3) K64, conjAut 3 K64 A ∈ E ∧ conjAut 3 K64 A ≠ 1 ∧
      Matrix.GeneralLinearGroup.det A = 1 := by
  have hlift : ∀ y : E, ∃ A : GL (Fin 3) K64, conjAut 3 K64 A = (y : MulAut (projectiveSL 3 K64)) :=
    fun y => MonoidHom.mem_range.mp (hEr y.2)
  choose A hA using hlift
  have hd : ∀ y : E, (Matrix.GeneralLinearGroup.det (A y)) ^ 21 ∈ rootsOfUnity 3 K64 := by
    intro y
    rw [mem_rootsOfUnity, ← pow_mul]
    have h63 : Matrix.GeneralLinearGroup.det (A y) ^ 63 = 1 := by
      rw [← CFSG.RankThree.PartTwo.Sec4.Res6L364.card_units_K64]
      exact pow_card_eq_one'
    simpa using h63
  let d : E → rootsOfUnity 3 K64 := fun y => ⟨_, hd y⟩
  have hnotinj : ¬ Function.Injective d := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective d hinj
    have h2 := card_rootsOfUnity K64 3
    omega
  rw [Function.Injective] at hnotinj
  push Not at hnotinj
  obtain ⟨y1, y2, hdeq, hne⟩ := hnotinj
  have hd12 : Matrix.GeneralLinearGroup.det (A y1) ^ 21 =
      Matrix.GeneralLinearGroup.det (A y2) ^ 21 := congrArg Subtype.val hdeq
  set C : GL (Fin 3) K64 := A y1 * (A y2)⁻¹ with hC
  have hC21 : (Matrix.GeneralLinearGroup.det C) ^ 21 = 1 := by
    rw [hC, map_mul, map_inv, mul_pow, inv_pow, hd12, mul_inv_cancel]
  have hl21 : ((Matrix.GeneralLinearGroup.det C : K64ˣ) : K64) ^ 21 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hC21, Units.val_one]
  obtain ⟨μ, hμ⟩ := CFSG.RankThree.PartTwo.Sec4.Res6L364.exists_cube_root hl21
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h] at hμ
    exact (Matrix.GeneralLinearGroup.det C).ne_zero (by rw [← hμ]; norm_num)
  set s : K64ˣ := Units.mk0 μ hμ0 with hs
  have hs3 : s ^ 3 = Matrix.GeneralLinearGroup.det C := Units.ext (by simpa [hs] using hμ)
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) s⁻¹ * C, ?_, ?_, ?_⟩
  · rw [map_mul, conjAut_scalar, one_mul, hC, map_mul, map_inv, hA, hA]
    exact E.mul_mem y1.2 (E.inv_mem y2.2)
  · rw [map_mul, conjAut_scalar, one_mul, hC, map_mul, map_inv, hA, hA]
    intro h
    apply hne
    exact Subtype.ext (mul_inv_eq_one.mp h)
  · rw [map_mul, det_scalar_three, inv_pow, ← hs3, inv_mul_cancel]

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
