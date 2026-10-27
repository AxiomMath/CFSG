module

public import CFSG.LocalAnalysis.UniquenessCase.UCK35w
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableAlt
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRee
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeSolv
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOutPPrime
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven
public import CFSG.RankThree.PartTwo.Sec14.Item148Solvable
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section OfK35


theorem k35w_of_k35 (hK : K35) : K35w := by
  intro G _ _ hX p hp hp2 M hM h2 hO
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p M
  obtain ⟨-, hcases⟩ := hK G hX p hp hp2 M hM (by omega) hO P hP
  rcases hcases with ⟨-, -, hM1⟩ | ⟨hAlt, -⟩ | ⟨-, -, hM3⟩ | ⟨n4, hshape4, hdvd4⟩ |
    ⟨-, -, hM5⟩ | ⟨hp5, hFi, -⟩ | ⟨-, -, hM7⟩ | ⟨-, -, hM8⟩
  · exact Or.inl (isPSolvable_of_normal_sylow hP hM1)
  · exact Or.inr (Or.inl hAlt)
  · exact Or.inl (isPSolvable_of_normal_sylow hP hM3)
  · exfalso
    have h2L : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(Opp p (⊤ : Subgroup G))) := by
      have h1 : CFSG.Open.pRank p (Opp p (⊤ : Subgroup G)) =
          CFSG.Open.pRank p (⊤ : Subgroup G) :=
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_pElementSubgroup hp ⊤
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, h1]
      exact h2
    obtain ⟨E, -, hEel, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup ↥(Opp p (⊤ : Subgroup G)))
    have hE2 : p ^ 2 ≤ Nat.card E := by
      rw [hEcard]
      exact Nat.pow_le_pow_right hp.pos h2L
    exact false_of_lieModel_twistedG2_of_dvd hshape4 hp hp2 hdvd4 hEel hE2
  · exact Or.inl (isPSolvable_of_normal_sylow hP hM5)
  · exact Or.inr (Or.inr ⟨hp5, hFi⟩)
  · exact Or.inl (isPSolvable_of_normal_sylow hP hM7)
  · exact Or.inl (isPSolvable_of_normal_sylow hP hM8)

end OfK35

section Holds


theorem k35w_holds
    : K35w := by
  intro G _ _ hX p hp hp2 M hM h2 hO
  by_cases hp3 : p = 3
  · subst hp3
    exact Or.inl (CFSG.RankThree.PartTwo.Sec14.isPSolvable_of_isSolvable Nat.prime_three
      (PartOne.Section7.isSolvable_of_isStronglyPEmbedded_three
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds hX hO h2 hM))
  · have hp5 : 5 ≤ p := by
      have h2' := hp.two_le
      by_contra h
      interval_cases p <;> simp_all (config := { decide := true })
    rcases PartOne.Section7.isSolvable_or_opp_alt_or_fi22_of_kFacts kFactSmallIdent_holds
        kFactOneLieTorus_holds stronglyEmbeddedCyclicOuter_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
        (CFSG.AGLEmbedding.kFactSmallOutPPrime_of_smallIdent kFactSmallIdent_holds)
        CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv hp hp5 hX hO h2 hM with
      hs | hA | hF
    · exact Or.inl (CFSG.RankThree.PartTwo.Sec14.isPSolvable_of_isSolvable hp hs)
    · exact Or.inr (Or.inl hA)
    · exact Or.inr (Or.inr hF)

end Holds

end CFSG.LocalAnalysis.UniquenessCase.UCK
