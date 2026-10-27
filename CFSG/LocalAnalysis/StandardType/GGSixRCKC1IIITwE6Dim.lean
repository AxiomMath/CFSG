module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6Card
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1LineAux
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatTypeDet
public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Open CFSG.Blueprint CFSG.StandardType
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Row


theorem card_centerQuot_ne_of_row_III {X : Type} [Group X] {J : Subgroup X}
    (hrow : GGSixRCKJRow .III J) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 5515776 ∧
      Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 174182400 ∧
      Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 211341312 ∧
      Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 25015379558400 := by
  obtain ⟨lab, hlab, R, _, I, F, θ, _, _, hr, hmodel⟩ :=
    largeEvenMarking_exists_markedModel hrow
  have hm : MarkedModel lab (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv θ.symm hmodel
  obtain ⟨hchar, hdeg, hshape⟩ := ggSixRCKLabelRow_III_parameters hlab hr
  have hm' : LieModel (↥J ⧸ Subgroup.center ↥J) (markTag lab) (markRank lab) 2 1 := by
    unfold MarkedModel at hm
    rwa [hchar, hdeg] at hm
  rcases hshape with ⟨ht, h3⟩ | ⟨ht, h4⟩
  · rw [ht] at hm'
    rw [CFSG.SeitzReduction.SymplecticPilot.card_of_lieModel_PSp_two_pow hm']
    have hm345 : markRank lab = 3 ∨ markRank lab = 4 ∨ 5 ≤ markRank lab := by omega
    rcases hm345 with h3' | h4' | hm5
    · rw [h3', CFSG.SeitzReduction.SymplecticPilot.ordBC_three_one_eq]
      decide
    · rw [h4', show CFSG.Open.ordBC 4 (2 ^ 1) = 47377612800 by decide]
      decide
    · have hpow : 2 ^ 21 ∣ CFSG.Open.ordBC (markRank lab) (2 ^ 1) := by
        obtain ⟨hdvd, -, -⟩ :=
          CFSG.SeitzReduction.SymplecticPilot.ordBC_two_pow_bounds
            (m := markRank lab) (f := 1) le_rfl
        have h25 : 21 ≤ 1 * (markRank lab * markRank lab) := by
          have := Nat.mul_le_mul hm5 hm5
          omega
        exact (Nat.pow_dvd_pow 2 h25).trans hdvd
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hc <;> rw [hc] at hpow <;> norm_num at hpow
  · rw [ht] at hm'
    rw [CFSG.SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow hm']
    have hn345 : markRank lab - 1 = 3 ∨ markRank lab - 1 = 4 ∨
        markRank lab - 1 = 5 ∨ 6 ≤ markRank lab - 1 := by omega
    rcases hn345 with h | h | h | h
    · rw [h, CFSG.SeitzReduction.UnitaryPilot.ordTwistedA_three_two_eq]
      decide
    · rw [h, CFSG.SeitzReduction.UnitaryPilot.ordTwistedA_four_two_eq]
      decide
    · rw [h, CFSG.SeitzReduction.TwistedE6Pilot.ordTwistedA_five_two_eq]
      decide
    · have hpow : 2 ^ 21 ∣ CFSG.Open.ordTwistedA (markRank lab - 1) (2 ^ 1) := by
        obtain ⟨hdvd, -, -⟩ :=
          CFSG.SeitzReduction.UnitaryPilot.ordTwistedA_two_pow_bounds
            (n := markRank lab - 1) (f := 1) (by omega) le_rfl
        have h21 : 21 ≤ 1 * ((markRank lab - 1) * (markRank lab - 1 + 1) / 2) := by
          have h42 : 6 * 7 ≤ (markRank lab - 1) * (markRank lab - 1 + 1) :=
            Nat.mul_le_mul h (by omega)
          have hdiv := Nat.div_le_div_right h42 (c := 2)
          norm_num at hdiv ⊢
          exact hdiv
        exact (Nat.pow_dvd_pow 2 h21).trans hdvd
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hc <;> rw [hc] at hpow <;> norm_num at hpow

end Row

section Dim


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem twE6MatFixDim_eq_36_or_28_of_row_III (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2)
    {h : twistedE6InndiagGL K σ} (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))))
    (hrow : GGSixRCKJRow .III J) :
    twE6MatFixDim K σ h = 36 ∨ twE6MatFixDim K σ h = 28 := by
  have hcard2 : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hchar : ringChar K = 2 :=
    CFSG.LieType.Chevalley.E6SecondGraphFixed.ringChar_eq_two_of_card
      (n := 2) (by norm_num) hcard2
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  obtain ⟨h24, h30, h36, h46⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S265.TE6.card_centerQuot_twE6Line_of_dim
      hK hσ hh3 hh1 hJ
  have hmem :=
    CFSG.StandardType.SCFourCover.twE6MatFixDim_mem_of_pow_three hK3 hh3 hh1
  have hne := card_centerQuot_ne_of_row_III hrow
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hd | hd | hd | hd | hd
  · exact absurd (h24 hd) hne.1
  · exact Or.inr hd
  · rcases h30 hd with h' | h'
    · exact absurd h' hne.2.1
    · exact absurd h' hne.2.2.1
  · exact Or.inl hd
  · exact absurd (h46 hd) hne.2.2.2

end Dim

end CFSG.StandardType.RCKC1
