module

public import CFSG.Quasithin.Background.E3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Counts
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem eight_le_mParam_of_forall_inverts (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Y : Subgroup (MulAut W)} (hY : ∃ t ∈ Y, orderOf t = 2)
    (h : ∀ t ∈ Y, orderOf t = 2 → ∃ x : MulAut W, orderOf x = p ∧ t * x * t⁻¹ = x⁻¹ ∧
      16 ≤ rk ↥(commSub ⊤ (zpowers x))) :
    8 ≤ E3.mParam Y := by
  classical
  refine SevenFour.le_mParam_of_forall hY ?_
  intro t htY ht
  obtain ⟨x, hx, htinv, h16⟩ := h t htY ht
  have hE : IsElemAbelian p (zpowers x) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  have hinv : ∀ y ∈ zpowers x, t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk := map_zpow (MulAut.conj t) x k
    simp only [MulAut.conj_apply] at hk
    rw [hk, htinv, inv_zpow]
  have hle := SevenFour.rk_commSub_le_two_mul_rkIdx hW hp hp2 hE ht hinv
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
