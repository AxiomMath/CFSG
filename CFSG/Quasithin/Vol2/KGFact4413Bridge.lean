module

public import CFSG.Quasithin.Vol2.KGFact4413Lie
public import CFSG.Quasithin.Vol2.Ch11SecBNPSyl
public import CFSG.Quasithin.Background.E1TwoAbs
public import CFSG.Quasithin.Background.E2TwoC

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem exists_lieCases_of_nParam (hC : E2.E22StatementC) {G : Type} [Group G] [Finite G]
    {H S MH : Subgroup G} (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : quasithinIsQTKECat G) (hO : pCoreOf 2 H ≠ ⊥) (hn : 1 < E1.nParam H)
    (hS : IsSylowTwoOf S H) (hU : IsUniqueMaxOver H S MH) :
    ∃ K ∈ cComp H, H = K ⊔ S ∧ E2.E22LieCases H S MH K := by
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hK hs hnab hO
  have hns : ¬ Group.IsSolvable ↥H := fun h => absurd hn (not_lt.mpr (E1.solvable_nParam_le_one h))
  have hnn : ¬ H ≤ Subgroup.normalizer (S : Set G) := by
    intro hNS
    have hTS : IsSylowIn 2 S H := ⟨hS.1, hS.2.1, hS.2.2⟩
    have hTn : (S.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hS.1).mpr hNS
    exact absurd hn (not_lt.mpr (Vol2.Ch11.SecB.nParam_le_one_of_normal_sylow hS.2.1 hS.1 hTn
      fun A hAH hA2 => E1.le_of_isSylowIn_of_normal hTS hTn hAH hA2))
  have hmin : MinParabolic H S MH := ⟨hS, hnn, hU⟩
  obtain ⟨⟨K, hKc, hHK, hq, hc⟩, hSQs⟩ := hC.1 G H S MH hmin hSQ hns
  have hnp := hC.2 G H S MH K hmin hSQ hns hKc hHK hq hc hSQs
  refine ⟨K, hKc, hHK, ?_⟩
  dsimp only [E2.E22CasesNoN] at hc
  dsimp only [E2.E22NParamCases] at hnp
  dsimp only [E2.E22LieCases]
  rcases hc with ⟨hJ, t, ht, hne, hM, ⟨n, hn2, hty, hB⟩ | ⟨p, hp, hp8, hK', hMK, haut⟩⟩ |
      ⟨hTK, hJ, ⟨n, hBen, hB⟩ | ⟨n, hn1, hK', hD, hB⟩ |
        ⟨p, e, hp, hp3, he, hpe8, hK', hMK, haut⟩ | ⟨p, hp, hp2, hK', hMK⟩⟩
  · exact Or.inl ⟨hJ, t, ht, hne, hM, n, hn2, hty, hB⟩
  · exfalso
    have h1 := (hnp.1 hJ ⟨t, ht, hne, hM⟩).2 p hp hp8 hK' hMK haut
    rw [h1] at hn
    exact lt_irrefl _ hn
  · exact Or.inr ⟨hTK, hJ, Or.inl ⟨n, hBen, hB⟩⟩
  · have hle := ((hnp.2 hTK hJ).2.1 n hn1 hK' hD hB).1
    have h1 : ((1 : ℕ) : ℕ∞) < n := by
      rw [Nat.cast_one]
      exact lt_of_lt_of_le hn hle
    have hge : 2 ≤ n := by
      have := ENat.natCast_lt_natCast.mp h1
      omega
    refine Or.inr ⟨hTK, hJ, Or.inr ⟨n, hge, ?_, hD, hB⟩⟩
    rcases hK' with hK' | hK'
    · exact Or.inl hK'
    · right
      rw [E2.IsSp4Prime] at hK'
      split_ifs at hK' with h1
      · omega
      · exact hK'
  · exfalso
    have h1 := (hnp.2 hTK hJ).2.2.1 p e hp hp3 he hpe8 hK' hMK haut
    rw [h1] at hn
    exact lt_irrefl _ hn
  · exfalso
    have h1 := (hnp.2 hTK hJ).2.2.2 p hp hp2 hK' hMK
    rw [h1] at hn
    exact lt_irrefl _ hn

namespace Ch4

theorem e22BorelFacts_of_lie (hC : E2.E22StatementC) (h : E22BorelFactsLie) : E22BorelFacts :=
  fun G _ _ H S MH hs hnab hK hO hn hS hU =>
    h G H S MH hs hnab hK hO (exists_lieCases_of_nParam hC hs hnab hK hO hn hS hU) hS hU

theorem lemma4413NA_of_lie (hC : E2.E22StatementC) (h : Lemma4413NALie) : Lemma4413NA :=
  fun G _ _ H S MH hs hnab hK hO hn hS hU =>
    h G H S MH hs hnab hK hO (exists_lieCases_of_nParam hC hs hnab hK hO hn hS hU) hS hU

end Ch4

theorem stmt4_4_13_of_lie (hC : E2.E22StatementC) (h : Stmt4_4_13Lie) : Stmt4_4_13 :=
  fun G _ _ H S MH hs hnab hK hO hn hS hU =>
    h G H S MH hs hnab hK hO (exists_lieCases_of_nParam hC hs hnab hK hO hn hS hU) hS hU

end CFSG.Quasithin.H13
