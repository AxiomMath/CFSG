module

public import CFSG.RankThree.PartOne.S11c.G2FiveFixed
public import CFSG.RankThree.PartOne.S11c.TrialityFiveFixed
public import CFSG.RankThree.PartOne.S11c.ETypeRankThree
public import CFSG.RankThree.PartOne.S11b.OddF4LocalRank
public import CFSG.RankThree.PartOne.S11.TenSevenKnown

public section

namespace CFSG.RankThree.PartOne.HNRed

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem not_dvd_ordF4_two : ¬ (126000 : ℕ) ∣ CFSG.Open.ordF4 2 := by
  unfold CFSG.Open.ordF4
  norm_num

theorem not_dvd_ordE6_two : ¬ (126000 : ℕ) ∣ CFSG.Open.ordE6 2 := by
  unfold CFSG.Open.ordE6
  norm_num

theorem five_fixed_card_dvd {T : Type} [Group T] (K : Subgroup T)
    (hK : StatedClassicalModel K .PSU 3 5 1) : (126000 : ℕ) ∣ Nat.card T := by
  have h1 := Subgroup.card_subgroup_dvd_card K
  rwa [(CFSG.RankThree.Classical.unitary_three_five_model K hK).1] at h1

theorem fiveFixedExcludesChevalley_holds
    : FiveFixedExcludesChevalley := by
  intro H _ _ hrank X hX β K hFive τ hτ ℓ f hmod
  have hK : StatedClassicalModel K .PSU 3 5 1 := hFive.2.2
  have hℓ : ℓ.Prime := hmod.1.1
  have hf : 1 ≤ f := hmod.1.2.1
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact g2_five_fixed_absurd hrank X hFive hmod
  ·
    by_cases h2 : ℓ = 2
    · subst h2
      obtain ⟨-, h2f, -, -⟩ := actualCoverHigherExceptionalSmallFieldRestrictions_of_repo H hrank X
        2 f hℓ hf .F4 (Or.inl rfl) hmod
      have hf2 : 2 ^ f = 2 := h2f rfl rfl
      have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 hmod.2
      rw [hf2] at hcard
      have := five_fixed_card_dvd K hK
      rw [hcard] at this
      exact not_dvd_ordF4_two this
    · obtain ⟨-, -, h4⟩ := oddF4ActualCoverLocalRankFour H X ℓ f hℓ h2 hf hmod
      omega
  ·
    obtain ⟨-, hℓ2, hf1⟩ := actualCoverETypeRankThreeOnlyE6FieldTwo H hrank X ℓ f hℓ hf .E6
      (Or.inl rfl) hmod
    subst hℓ2
    subst hf1
    have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_E6 hmod.2
    have := five_fixed_card_dvd K hK
    rw [hcard] at this
    exact not_dvd_ordE6_two (by simpa using this)
  ·
    obtain ⟨h, -⟩ := actualCoverETypeRankThreeOnlyE6FieldTwo H hrank X ℓ f hℓ hf .E7
      (Or.inr (Or.inl rfl)) hmod
    exact absurd h (by decide)
  ·
    obtain ⟨h, -⟩ := actualCoverETypeRankThreeOnlyE6FieldTwo H hrank X ℓ f hℓ hf .E8
      (Or.inr (Or.inr (Or.inl rfl))) hmod
    exact absurd h (by decide)
  ·
    obtain ⟨h, -⟩ := actualCoverETypeRankThreeOnlyE6FieldTwo H hrank X ℓ f hℓ hf .twistedE6
      (Or.inr (Or.inr (Or.inr rfl))) hmod
    exact absurd h (by decide)
  ·
    obtain ⟨-, -, hℓ23, -⟩ := actualCoverHigherExceptionalSmallFieldRestrictions_of_repo H hrank X
      ℓ f hℓ hf .trialityD4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hmod
    rcases hℓ23 rfl with rfl | rfl
    · exact triality_five_fixed_absurd K hK hf hmod.2
    · obtain ⟨-, -, h4⟩ := charThreeTrialityActualCoverLocalRankFour_of_repo H X f hmod
      omega

end CFSG.RankThree.PartOne.HNRed
