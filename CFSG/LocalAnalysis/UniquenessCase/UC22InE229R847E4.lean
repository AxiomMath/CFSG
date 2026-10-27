module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z9
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847E4 (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.card X = q →
    ∀ p ∈ D.sig, (F08.Thin8 Y ∨ ∃ n : ℕ, IsSU3 (Bar2 Y) n ∧ 2 ^ (2 * n) ≡ 1 [MOD q]) →
      normalizer (X : Set G) ≤ D.M

@[expose] def R847U3Three (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, ∀ X : Subgroup G, X ≤ Y → Nat.card X = 3 → ∀ n : ℕ, IsSU3 (Bar2 Y) n →
    3 ∣ 2 ^ n + 1 → normalizer (X : Set G) ≤ D.M

theorem r847E4_of_r847 (D : Data G) (h847 : F08.R847 D) (he : 3 < evenRank G) : R847E4 D := by
  intro Y hY X hXY q hq hq2 hXq p hp hcase
  rcases h847 Y hY X hXY q hq hq2 hXq p hp hcase with h1 | h2 | h3
  · exact h1
  · obtain ⟨_, _, _, _, _, he3, _⟩ := h2
    omega
  · obtain ⟨_, _, _, _, _, he3, _⟩ := h3
    omega

theorem r847_of_r847E4 {D : Data G} (h : R847E4 D) : F08.R847 D :=
  fun Y hY X hXY q hq hq2 hXq p hp hcase => Or.inl (h Y hY X hXY q hq hq2 hXq p hp hcase)

theorem r847Four_of_r847E4 {D : Data G} (h : R847E4 D) : R847Four D :=
  fun Y hY X hXY q hq hq2 hXq p hp hthin => h Y hY X hXY q hq hq2 hXq p hp (Or.inl hthin)

theorem r847E4_setup4_of_five_le (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ)
    (hB3 : BadNoStrongThree) (hThin : PartTwo.ThinList13)
    (hOut : RankThreeTheoremC.KFactOutCyclic) (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hgr : GriessAllModelsStatement) (hC : uc22pwCartanSU3)
    (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S)) (h3 : R847U3Three (UC6.dataOfSetup4 hS hU S))
    (h5 : ∃ p ∈ (UC6.dataOfSetup4 hS hU S).sig, 5 ≤ p) : R847E4 (UC6.dataOfSetup4 hS hU S) := by
  obtain ⟨p, hp, hp5⟩ := h5
  intro Y hY X hXY q hq hq2 hXc _ _ hcase
  rcases hcase with hthin | ⟨n, hYn, hmod⟩
  · exact uc22ine229_normalizer_le_of_thin_setup4 hSE hSEZ hB3 hThin hOut hS hU S hσ hp hp5 hY
      hthin hq hq2 hXY hXc
  have hdvd : q ∣ (2 ^ n + 1) * (2 ^ n - 1) := by
    have h := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      zify [h1, h2]
      ring
    rwa [hfac] at h
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with hqn | hqn
  · by_cases hq3 : q = 3
    · subst hq3
      exact h3 Y hY X hXY hXc n hYn hqn
    · have hq3' : 3 < q := by
        have := hq.two_le
        omega
      haveI : Fact q.Prime := ⟨hq⟩
      have hX1 : X ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hXc
        exact hq.one_lt.ne hXc
      exact (h846 Y hY n hYn q hq hq3' hqn).normalizer_le hX1
        (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])) (hXY.trans hY.1.le)
  · exact uc22ine229_normalizer_le_of_isSU3_setup4 hSE hSEZ hB3 hS hU S hσ hgr hC hp hp5 hY hYn
      hq hq2 hqn hXY hXc

theorem uc22ine229_exists_five_le_of_not_forall {D : Data G}
    (h : ¬ ∀ p ∈ D.sig, p = 3) : ∃ p ∈ D.sig, 5 ≤ p := by
  obtain ⟨p, hp, hp3⟩ : ∃ p ∈ D.sig, p ≠ 3 := by
    by_contra h'
    exact h fun p hp => by_contra fun hne => h' ⟨p, hp, hne⟩
  have hpP := D.sig_prime p hp
  exact ⟨p, hp, hpP.1.five_le_of_ne_two_of_ne_three hpP.2 hp3⟩

theorem r847E4_setup4 (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ)
    (hB3 : BadNoStrongThree) (hThin : PartTwo.ThinList13)
    (hOut : RankThreeTheoremC.KFactOutCyclic) (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hgr : GriessAllModelsStatement) (hC : uc22pwCartanSU3)
    (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S)) (h3 : R847U3Three (UC6.dataOfSetup4 hS hU S))
    (hres : (∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig, p = 3) →
      R847E4 (UC6.dataOfSetup4 hS hU S)) : R847E4 (UC6.dataOfSetup4 hS hU S) := by
  by_cases hall : ∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig, p = 3
  · exact hres hall
  · exact r847E4_setup4_of_five_le hSE hSEZ hB3 hThin hOut hS hU S hσ hgr hC h846 h3
      (uc22ine229_exists_five_le_of_not_forall hall)

end CFSG.LocalAnalysis.UniquenessCase.UC22
