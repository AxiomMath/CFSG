module

public import CFSG.LocalAnalysis.WeakClosure81.W115Trans
public import CFSG.LocalAnalysis.WeakClosure81.W115Gen
public import CFSG.Quasithin.Background.SmithB45MatM22
public import CFSG.LocalAnalysis.WeakClosure81.W115WeakDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w4Lem11_5Weak_holds :
    W4Lem11_5Weak := by
  classical
  intro W _ _ hW Y L hLY hnorm hF hq hO2 hM hirr
  by_cases hcard : Nat.card W ≤ 2 ^ 30
  · right
    have hmul : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
    have hirrFun : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
      fun U hU => hirr.2.2.2 U hU bot_le le_top
    have h10 : Nat.card W = 2 ^ 10 := by
      rcases CFSG.Quasithin.mathieuSmallIrr22_holds W hmul L hM hirrFun hcard with hc | hc
      · obtain ⟨e, -⟩ := CFSG.Quasithin.H.Mathieu.code22_std hc
        rw [Nat.card_congr e.toEquiv]
        simp
      · obtain ⟨e, -⟩ := CFSG.Quasithin.H.Mathieu.cocode22_std hc
        rw [Nat.card_congr e.toEquiv]
        simp
    have h2 := card_eq_two_pow_rk hW
    rw [h10] at h2
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  · left
    have hrk : 31 ≤ rk W := by
      have h2 := card_eq_two_pow_rk hW
      by_contra hlt
      push Not at hlt
      apply hcard
      rw [h2]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hL1 : L ≠ ⊥ := by
      intro h
      obtain ⟨a, b, hab⟩ := hq.2.2
      have hsub : Subsingleton ↥L := by rw [h]; infer_instance
      have : Subsingleton (↥L ⧸ Subgroup.center ↥L) := inferInstance
      exact hab (Subsingleton.elim (a * b) (b * a))
    have hfix : fixV L = ⊥ := w115_fixV_eq_bot_of_isIrrOn hirr hL1
    unfold E3.mParam
    by_cases hEven : Even (Nat.card Y)
    · rw [if_pos hEven]
      refine le_csInf ?_ ?_
      · obtain ⟨t, hto⟩ :=
          exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
        exact ⟨_, (t : MulAut W), t.2, by rwa [Subgroup.orderOf_coe], rfl⟩
      · rintro n ⟨t, htY, hto, rfl⟩
        obtain ⟨b, hb⟩ := w115_fourConj_of_isSpor hLY hnorm hF hM htY hto
        have h4 := w115_rk_le_four_mul hW hfix
          (fun i => ((b i : ↥L) : MulAut W) * t * ((b i : ↥L) : MulAut W)⁻¹)
          (fun i => ⟨_, rfl⟩) hb
        omega
    · rw [if_neg hEven]
      omega

end CFSG.LocalAnalysis.WeakClosure81.W115
