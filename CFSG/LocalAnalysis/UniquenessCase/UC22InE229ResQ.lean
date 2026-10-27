module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R847E4
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847ResQ (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → 5 ≤ q → Nat.card X = q →
    (F08.Thin8 Y ∨ ∃ n : ℕ, IsSU3 (Bar2 Y) n ∧ q ∣ 2 ^ n - 1) → normalizer (X : Set G) ≤ D.M

theorem r847E4_of_resQ (D : Data G) (hSg : UC6S846.SigmaStd D) (h846 : F08.R846 D)
    (hall : ∀ p ∈ D.sig, p = 3) (hQ : R847ResQ D) : R847E4 D := by
  intro Y hY X hXY q hq hq2 hXc _ _ hcase
  have hYM : Y ≤ D.M := hY.1.le
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  have hXp : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  by_cases hq3 : q = 3
  · subst hq3
    obtain ⟨p, hp⟩ := hSg.nonempty
    have hp3 : p = 3 := hall p hp
    subst hp3
    exact (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp).normalizer_le hX1
      hXp (hXY.trans hYM)
  have hq5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three hq2 hq3
  rcases hcase with hthin | ⟨n, hYn, hmod⟩
  · exact hQ Y hY X hXY q hq hq5 hXc (Or.inl hthin)
  have hdvd : q ∣ (2 ^ n + 1) * (2 ^ n - 1) := by
    have h := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      zify [h1, h2]
      ring
    rwa [hfac] at h
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with hqn | hqn
  · haveI : Fact q.Prime := ⟨hq⟩
    exact (h846 Y hY n hYn q hq (by omega) hqn).normalizer_le hX1 hXp (hXY.trans hYM)
  · exact hQ Y hY X hXY q hq hq5 hXc (Or.inr ⟨n, hYn, hqn⟩)

theorem r847E4_setup4_of_resQ (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ)
    (hB3 : BadNoStrongThree) (hThin : PartTwo.ThinList13)
    (hOut : RankThreeTheoremC.KFactOutCyclic) (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hgr : GriessAllModelsStatement) (hC : uc22pwCartanSU3)
    (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S)) (h3 : R847U3Three (UC6.dataOfSetup4 hS hU S))
    (hQ : (∀ p ∈ (UC6.dataOfSetup4 hS hU S).sig, p = 3) →
      R847ResQ (UC6.dataOfSetup4 hS hU S)) : R847E4 (UC6.dataOfSetup4 hS hU S) :=
  r847E4_setup4 hSE hSEZ hB3 hThin hOut hS hU S hσ hgr hC h846 h3 fun hall =>
    r847E4_of_resQ _ (UC6S846.sigmaStd_dataOfSetup4 hS hU S) h846 hall (hQ hall)

end CFSG.LocalAnalysis.UniquenessCase.UC22
