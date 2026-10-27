module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Defs
public import CFSG.RankThree.SubgroupLists.SL2Perfect
public import CFSG.Walter.JRFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

open Subgroup

private theorem oddIdxRest_three_dvd_sq_sub_one {q : ℕ} (h : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have h0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact h (dvd_zero 3))
  have h1 : q ^ 2 % 3 = 1 := by
    have hne : q % 3 ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
    have hlt : q % 3 < 3 := Nat.mod_lt q (by norm_num)
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h' | h' <;> rw [Nat.pow_mod, h']
  have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h0
  omega

private theorem oddIdxRest_card_center_sl2_dvd_two (F : Type) [Field F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∣ 2 := by
  by_cases h2 : (2 : F) = 0
  · have hbot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro A hA
      obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
      rw [Fintype.card_fin] at hr
      have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
      have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h5)
      subst hr1
      ext i j
      simpa [Matrix.scalar_apply, Matrix.one_apply] using (congrFun (congrFun hrA i) j).symm
    rw [hbot, Subgroup.card_bot]
    exact one_dvd 2
  · rw [CFSG.RankThree.SubgroupLists.natCard_center_sl2 h2]

private theorem oddIdxRest_dvd_check : ∀ q ∈ Nat.divisors 1280, 4 ≤ q →
    q * (q ^ 2 - 1) ∣ 103680 → q = 4 ∨ q = 5 := by
  decide +kernel

theorem oddIdxRest_card_eq_four_or_five {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (h3 : ¬ 3 ∣ Nat.card F)
    (hcat : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∣ 51840 ∨
      ¬ 3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    Nat.card F = 4 ∨ Nat.card F = 5 := by
  have h3sq : 3 ∣ Nat.card F ^ 2 - 1 := oddIdxRest_three_dvd_sq_sub_one h3
  have hc : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∣ 2 :=
    oddIdxRest_card_center_sl2_dvd_two F
  have hcard : Nat.card F * (Nat.card F ^ 2 - 1) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    have h1 := CFSG.GorensteinWalter.sl2_card_formula F
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
    rw [h1] at h2
    exact h2
  have h3P : 3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    have h3Pc : 3 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
      rw [← hcard]
      exact dvd_mul_of_dvd_right h3sq _
    have hcop : Nat.Coprime 3
        (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) :=
      Nat.Coprime.of_dvd_right hc (by norm_num : Nat.Coprime 3 2)
    exact (hcop.dvd_mul_right).mp h3Pc
  have hP : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∣ 51840 := by
    rcases hcat with hdvd | hnot
    · exact hdvd
    · exact absurd h3P hnot
  have hprod : Nat.card F * (Nat.card F ^ 2 - 1) ∣ 103680 := by
    have hmul : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∣ 51840 * 2 :=
      mul_dvd_mul hP hc
    rw [hcard, show (103680 : ℕ) = 51840 * 2 by norm_num]
    exact hmul
  have hq103 : Nat.card F ∣ 103680 :=
    (dvd_mul_right (Nat.card F) (Nat.card F ^ 2 - 1)).trans hprod
  have hcop3 : Nat.Coprime (Nat.card F) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
  have hcop81 : Nat.Coprime (Nat.card F) 81 := by
    simpa using (Nat.coprime_pow_right_iff (by norm_num : 0 < 4) (Nat.card F) 3).mpr hcop3
  have hq1280 : Nat.card F ∣ 1280 := by
    have h' : Nat.card F ∣ 1280 * 81 := by
      rwa [show (1280 * 81 : ℕ) = 103680 by norm_num]
    exact (hcop81.dvd_mul_right).mp h'
  exact oddIdxRest_dvd_check (Nat.card F)
    (Nat.mem_divisors.mpr ⟨hq1280, by norm_num⟩) h4 hprod

theorem oddIdxRest_card_of_sl2_section {Γ : Type} [Group Γ] {N W₁ : Subgroup Γ} (hW₁ : W₁ ≤ N)
    {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) (h3 : ¬ 3 ∣ Nat.card F)
    (φ : ↥W₁ →* Matrix.SpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ)
    (hN : CFSG.KCore.KGroupNonab (DvdOrThreeFree 51840) ↥N) :
    Nat.card F = 4 ∨ Nat.card F = 5 := by
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hnonab : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, a * b ≠ b * a :=
    CFSG.Walter.psl2_exists_mul_ne_mul F h4
  let ψ : ↥(W₁.subgroupOf N) →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
      (φ.comp (Subgroup.subgroupOfEquivOfLe hW₁).toMonoidHom)
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp
      (hφ.comp (Subgroup.subgroupOfEquivOfLe hW₁).surjective)
  have hcat := hN.catalogue_of_surjective (isoInvariant_dvdOrThreeFree 51840)
    (W₁.subgroupOf N) hnonab ψ hψ
  exact oddIdxRest_card_eq_four_or_five h4 h3 hcat

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx
