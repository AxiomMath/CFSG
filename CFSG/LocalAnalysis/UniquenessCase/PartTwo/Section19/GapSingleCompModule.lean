module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoDirSum
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenGrp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81 (stableUnder_commSub fixV_eq_bot_of_normal)

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem commSub_top_eq_top_of_isIrrOn {Y N : Subgroup (MulAut W)} (hirr : IsIrrOn Y ⊤ ⊥)
    (hnorm : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) (hN : N ≠ ⊥) : commSub ⊤ N = ⊤ := by
  rcases hirr.2.2.2 (commSub ⊤ N) (stableUnder_commSub hnorm hirr.2.1) bot_le le_top with
    h | h
  · exfalso
    have h1 : (⊤ : Subgroup W) ≤ fixV N := commSub_eq_bot_iff.mp h
    rw [fixV_eq_bot_of_normal (fun Z hZ => hirr.2.2.2 Z hZ bot_le le_top) hnorm hN] at h1
    exact lt_irrefl _ (lt_of_lt_of_le hirr.1 h1)
  · exact h

theorem normalizerMonoidHom_ne_one_of_rkIdx_lt_dMinDeg (hW : ∀ w : W, w ^ 2 = 1)
    {Y N : Subgroup (MulAut W)} (hirr : IsIrrOn Y ⊤ ⊥)
    (hYN : Y ≤ normalizer (N : Set (MulAut W))) (hN : N ≠ ⊥) {t : MulAut W} (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (htd : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥N) :
    N.normalizerMonoidHom ⟨t, hYN htY⟩ ≠ 1 := by
  have hnorm : ∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.mp (hYN hy) n).mp hn
  intro h1
  have hc : ∀ n ∈ N, t * n = n * t := by
    intro n hn
    have h2 : ((N.normalizerMonoidHom ⟨t, hYN htY⟩ ⟨n, hn⟩ : ↥N) : MulAut W) = n := by
      rw [h1]
      rfl
    rw [N.normalizerMonoidHom_apply_apply_coe] at h2
    calc t * n = t * n * t⁻¹ * t := by group
      _ = n * t := by rw [h2]
  have hU : StableUnder N (fixV (Subgroup.zpowers t)) := by
    intro n hn w hw
    rw [mem_fixV_zpowers_iff_apply] at hw ⊢
    have h3 : (t * n) w = (n * t) w := by rw [hc n hn]
    simp only [MulAut.mul_apply, hw] at h3
    exact h3
  have hle := Inputs1719.commSub_le_of_rk_lt_dMinDeg hW (K := N) le_top
    (fun _ _ _ _ => Subgroup.mem_top _) hU (by
      have := rk_add_rkIdx (fixV (Subgroup.zpowers t))
      rw [rk_top]
      omega)
  rw [commSub_top_eq_top_of_isIrrOn hirr hnorm hN, top_le_iff] at hle
  have ht1 : t = 1 := by
    ext w
    have hw : w ∈ fixV (Subgroup.zpowers t) := hle ▸ Subgroup.mem_top w
    exact mem_fixV_zpowers_iff_apply.mp hw
  rw [ht1, orderOf_one] at ht2
  exact absurd ht2 (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
