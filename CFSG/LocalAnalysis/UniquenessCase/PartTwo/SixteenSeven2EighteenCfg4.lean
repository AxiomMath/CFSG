module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Unif
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9Idx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c167_mQuot_le_rkIdx (hW : ∀ w : W, w ^ 2 = 1) (J C : Subgroup W) :
    E3.mQuot J (J ⊓ C) ≤ rkIdx C := by
  have hJ : rk ↥J = E3.mQuot J (J ⊓ C) + rk ↥(J ⊓ C) := by
    have hh := E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hW).to_subgroup J)
      (inf_le_left : J ⊓ C ≤ J)
    rw [card_eq_two_pow hW, card_eq_two_pow hW, ← pow_add] at hh
    exact Nat.pow_right_injective (le_refl 2) hh
  have hidx : rk ↥C + rkIdx C = rk W := rk_add_rkIdx C
  have hsupinf : rk ↥(J ⊔ C) + rk ↥(J ⊓ C) = rk ↥J + rk ↥C := rk_sup_add_rk_inf J C
  have hle : rk ↥(J ⊔ C) ≤ rk W := by
    have h := rk_mono (G := W) (le_top : J ⊔ C ≤ ⊤)
    rwa [rk_top] at h
  omega

theorem s16c167_cfg4_abstract {X L : Subgroup (MulAut W)} {Z : Subgroup W}
    (F : Cfg4Setting X L Z) :
    2 ≤ E3.mParam X ∧
      (∀ Y₁ ∈ conjSubs X Z, ∀ Y₂ ∈ conjSubs X Z, Y₁ ≠ Y₂ → rk ↥(Y₁ ⊔ Y₂) = 4) ∧
      (∀ t ∈ X, t * t = 1 → ∀ Y₁ ∈ conjSubs X Z, ∀ Y₂ ∈ conjSubs X Z, Y₁ ≠ Y₂ →
        (Y₁ ⊔ Y₂).map t.toMonoidHom = Y₁ ⊔ Y₂ →
          Y₁ ⊔ Y₂ ≤ fixV (Subgroup.zpowers t) ∨
            2 ≤ E3.mQuot (Y₁ ⊔ Y₂) ((Y₁ ⊔ Y₂) ⊓ fixV (Subgroup.zpowers t))) := by
  have hpair : ∀ Y₁ ∈ conjSubs X Z, ∀ Y₂ ∈ conjSubs X Z, ∀ Y ∈ conjSubs X Z,
      Y ≤ Y₁ ⊔ Y₂ → Y = Y₁ ∨ Y = Y₂ := by
    intro Y₁ hY₁ Y₂ hY₂ Y hY hle
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hne₁, hne₂⟩ := hcon
    have hsub : ({Y₁, Y₂} : Set (Subgroup W)) ⊆ conjSubs X Z \ {Y} := by
      intro A hA
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
      rcases hA with rfl | rfl
      · exact ⟨hY₁, fun h => hne₁ h.symm⟩
      · exact ⟨hY₂, fun h => hne₂ h.symm⟩
    have hle' : Y₁ ⊔ Y₂ ≤ sSup (conjSubs X Z \ {Y}) :=
      sup_le (le_sSup (hsub (by simp))) (le_sSup (hsub (by simp)))
    have hdisj : Disjoint Y (sSup (conjSubs X Z \ {Y})) := F.indep hY
    have hbot : Y = ⊥ := disjoint_self.mp (hdisj.mono_right (le_trans hle hle'))
    have h2 : rk ↥Y = 2 := by rw [s16c167_cfg4_rk_mem hY, F.rk_eq]
    rw [hbot, rk_bot] at h2
    omega
  refine ⟨?_, ?_, ?_⟩
  · refine s16c167_le_mParam X (n := 2) ?_ ?_
    · intro t htX ht htne
      by_cases hcase : ∃ Y ∈ conjSubs X Z, Y.map t.toMonoidHom ≠ Y
      · obtain ⟨Y, hY, hYt⟩ := hcase
        have hYtmem : Y.map t.toMonoidHom ∈ conjSubs X Z := s16c167_cfg4_map_mem htX hY
        have hinf : Y ⊓ Y.map t.toMonoidHom = ⊥ :=
          s16c167_cfg4_inf_eq_bot F.indep hY hYtmem hYt.symm
        have h := s16c167_rk_le_rkIdx_of_inf_map_eq_bot t (I := Y) hinf
        have h2 : rk ↥Y = 2 := by rw [s16c167_cfg4_rk_mem hY, F.rk_eq]
        omega
      · have hstab : ∀ Y ∈ conjSubs X Z, Y.map t.toMonoidHom = Y := by
          intro Y hY
          by_contra h
          exact hcase ⟨Y, hY, h⟩
        have hex : ∃ Y₁ ∈ conjSubs X Z, ¬ Y₁ ≤ fixV (Subgroup.zpowers t) := by
          by_contra hcon
          have hall : ∀ Y ∈ conjSubs X Z, Y ≤ fixV (Subgroup.zpowers t) := by
            intro Y hY
            by_contra h
            exact hcon ⟨Y, hY, h⟩
          have hsup : sSup (conjSubs X Z) ≤ fixV (Subgroup.zpowers t) := sSup_le hall
          have htop : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers t) := by
            rw [← F.sup_eq]
            exact hsup
          have hCtop : fixV (Subgroup.zpowers t) = ⊤ := top_le_iff.mp htop
          have ht1 : t = 1 := by
            ext w
            have hw : w ∈ fixV (Subgroup.zpowers t) := by rw [hCtop]; trivial
            simpa using (mem_fixV_zpowers t w).mp hw
          exact htne ht1
        obtain ⟨Y₁, hY₁, hY₁C⟩ := hex
        obtain ⟨Y₂, hY₂, hne⟩ := Set.exists_ne_of_one_lt_ncard (s := conjSubs X Z)
          (by rw [F.ncard_eq]; norm_num) Y₁
        have hne' : Y₁ ≠ Y₂ := hne.symm
        have hunif := s16c167_cfg4_unif F htX ht hY₁ hY₂ hne'
          (hstab Y₁ hY₁) (hstab Y₂ hY₂)
        have hY₂C : ¬ Y₂ ≤ fixV (Subgroup.zpowers t) := fun h => hY₁C (hunif.mpr h)
        have hsplit := s16c167_mQuot_sup_split F.sq t (A := Y₁) (B := Y₂)
          (s16c167_cfg4_inf_eq_bot F.indep hY₁ hY₂ hne') (hstab Y₁ hY₁) (hstab Y₂ hY₂)
        have h1 := s16c167_one_le_mQuot_of_not_le F.sq t (A := Y₁) hY₁C
        have h2 := s16c167_one_le_mQuot_of_not_le F.sq t (A := Y₂) hY₂C
        have hle := s16c167_mQuot_le_rkIdx F.sq (Y₁ ⊔ Y₂) (fixV (Subgroup.zpowers t))
        omega
    · have h := rk_mono (G := W) (le_top : Z ≤ ⊤)
      rw [rk_top, F.rk_eq] at h
      exact h
  · intro Y₁ hY₁ Y₂ hY₂ hne
    have hdisj : Y₁ ⊓ Y₂ = ⊥ := s16c167_cfg4_inf_eq_bot F.indep hY₁ hY₂ hne
    have h1 : rk ↥Y₁ = 2 := by rw [s16c167_cfg4_rk_mem hY₁, F.rk_eq]
    have h2 : rk ↥Y₂ = 2 := by rw [s16c167_cfg4_rk_mem hY₂, F.rk_eq]
    have hsup := rk_sup_add_rk_inf Y₁ Y₂
    rw [hdisj, rk_bot] at hsup
    omega
  · intro t htX ht Y₁ hY₁ Y₂ hY₂ hne hI
    have hY₁t : Y₁.map t.toMonoidHom ∈ conjSubs X Z := s16c167_cfg4_map_mem htX hY₁
    have hY₂t : Y₂.map t.toMonoidHom ∈ conjSubs X Z := s16c167_cfg4_map_mem htX hY₂
    have hle₁ : Y₁.map t.toMonoidHom ≤ Y₁ ⊔ Y₂ := by
      have h := Subgroup.map_mono (f := t.toMonoidHom) (le_sup_left : Y₁ ≤ Y₁ ⊔ Y₂)
      rwa [hI] at h
    have hle₂ : Y₂.map t.toMonoidHom ≤ Y₁ ⊔ Y₂ := by
      have h := Subgroup.map_mono (f := t.toMonoidHom) (le_sup_right : Y₂ ≤ Y₁ ⊔ Y₂)
      rwa [hI] at h
    rcases hpair Y₁ hY₁ Y₂ hY₂ (Y₁.map t.toMonoidHom) hY₁t hle₁ with ht₁ | ht₁
    · have ht₂ : Y₂.map t.toMonoidHom = Y₂ := by
        rcases hpair Y₁ hY₁ Y₂ hY₂ (Y₂.map t.toMonoidHom) hY₂t hle₂ with h | h
        · exfalso
          apply hne
          have hinj : Function.Injective (Subgroup.map t.toMonoidHom) :=
            Subgroup.map_injective (f := t.toMonoidHom) t.injective
          have heq : Y₂.map t.toMonoidHom = Y₁.map t.toMonoidHom := by rw [h, ht₁]
          exact (hinj heq).symm
        · exact h
      have hunif := s16c167_cfg4_unif F htX ht hY₁ hY₂ hne ht₁ ht₂
      by_cases hc₁ : Y₁ ≤ fixV (Subgroup.zpowers t)
      · left
        exact sup_le hc₁ (hunif.mp hc₁)
      · right
        have hc₂ : ¬ Y₂ ≤ fixV (Subgroup.zpowers t) := fun h => hc₁ (hunif.mpr h)
        have hsplit := s16c167_mQuot_sup_split F.sq t (A := Y₁) (B := Y₂)
          (s16c167_cfg4_inf_eq_bot F.indep hY₁ hY₂ hne) ht₁ ht₂
        have h1 := s16c167_one_le_mQuot_of_not_le F.sq t (A := Y₁) hc₁
        have h2 := s16c167_one_le_mQuot_of_not_le F.sq t (A := Y₂) hc₂
        omega
    · right
      have hinf : Y₁ ⊓ Y₁.map t.toMonoidHom = ⊥ := by
        rw [ht₁]
        exact s16c167_cfg4_inf_eq_bot F.indep hY₁ hY₂ hne
      have h := s16c167_rk_le_mQuot_of_inf_map_eq_bot F.sq t (J := Y₁ ⊔ Y₂) (R := Y₁)
        le_sup_left hinf
      have h2 : rk ↥Y₁ = 2 := by rw [s16c167_cfg4_rk_mem hY₁, F.rk_eq]
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
