module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ONanLocal17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicLocal17
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Rank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicRankData
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.CaseM22Dispatch
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem k_ONanQuotThreeRank_holds :
    K_ONanQuotThreeRank := by
  intro X _ _ hX
  obtain ⟨e⟩ := hX
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.ON_elementary_three_rank_four
  exact CFSG.HardMathSupport.Timmesfeld.Coordinator.le_pRank_of_mulEquiv (by norm_num) e.symm hE hc

theorem k_M22OddCover_holds :
    K_M22OddCover := by
  intro X _ _ hq hodd hM22
  obtain ⟨e⟩ := hM22
  refine ⟨?_, ?_⟩
  · rintro ⟨f⟩
    have h1 : Nat.card (X ⧸ Subgroup.center X) = 443520 :=
      (Nat.card_congr e.toEquiv).trans
        CFSG.HardMathSupport.Timmesfeld.Coordinator.card_nativeM22
    have h2 : Nat.card X = 604800 := (Nat.card_congr f.toEquiv).trans CFSG.Sporadic.J2.card_J2
    have h3 := Subgroup.card_quotient_dvd_card (Subgroup.center X)
    rw [h1, h2] at h3
    omega
  · have : Group.IsPerfect X := Group.isPerfect_def.mpr hq.1
    rcases CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.m22_center_card_odd_cases
      hodd e with h | h
    · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h)
    · exact Or.inr h

theorem k_SporadicThreeRankPos_holds :
    K_SporadicThreeRankPos := by
  intro X _ _ _ s h
  obtain ⟨e⟩ := h
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv X e.toEquiv
  by_cases hsq : s ∈ CFSG.SectionRank.sqtkSporadicNames
  · simp only [CFSG.SectionRank.sqtkSporadicNames, Finset.mem_insert,
      Finset.mem_singleton] at hsq
    rcases hsq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_three_of_isSpor_M11 (X := X) ⟨e⟩)
    · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_three_of_isSpor_M12 (X := X) ⟨e⟩)
    · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_three_of_isSpor_M22 (X := X) ⟨e⟩)
    · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_three_of_isSpor_M23 (X := X) ⟨e⟩)
    · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_three_of_isSpor_M24 (X := X) ⟨e⟩)
    · have hcardX : Nat.card X = 175560 :=
        (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hcardX]; norm_num)
      exact CFSG.Quasithin.A3Facts.one_le_pRank_of_orderOf Nat.prime_three hx
    · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_three_of_isSpor_J2 (X := X) ⟨e⟩)
    · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_three_of_isSpor_J4 (X := X) ⟨e⟩)
    · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_three_of_isSpor_HS (X := X) ⟨e⟩)
    · have hcardX : Nat.card X = 4030387200 :=
        (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.He.card_He
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hcardX]; norm_num)
      exact CFSG.Quasithin.A3Facts.one_le_pRank_of_orderOf Nat.prime_three hx
    · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_three_of_isSpor_Ru (X := X) ⟨e⟩)
  · by_cases hM : s = .M
    · subst hM
      have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M) := Finite.of_equiv X e.toEquiv
      have hnt : Nontrivial (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
        e.symm.toEquiv.nontrivial
      have : Nontrivial CFSG.Blueprint.NativeSporadic.M := hnt
      obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.M_nontrivial_elementary_three_rank_four
      let E' : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .M) := E
      have hE' : CFSG.Open.IsElemAbelian 3 E' := hE
      have hcard' : Nat.card E' = 3 ^ 4 := hcard
      have h : 3 ≤ CFSG.Open.pRank 3
          (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .M)) :=
        le_trans (by norm_num : 3 ≤ 4)
          (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E') (k := 4) (by norm_num)
            le_top hE' hcard')
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
      exact le_trans (by norm_num : 1 ≤ 3) h
    · obtain ⟨E, hE, k, hk, hcard⟩ :=
        CFSG.SectionRank.sporadicThreeRankWitnesses s hsq hM
      have h : 1 ≤ CFSG.Open.pRank 3
          (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier s)) :=
        le_trans (by omega : 1 ≤ k)
          (CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E) (k := k) (by norm_num)
            le_top hE hcard)
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
      exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
