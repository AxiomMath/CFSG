module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Five
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Opp R72Shape)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (QuotK7 ImageModK LKQuot7 IsReeType)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree (Gls3ConclusionPlus)

variable {G : Type} [Group G] [Finite G]


theorem r72_of_core (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hOutP : CFSG.AGLEmbedding.KFactSmallOutPPrime)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hR3 : ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ → IsoLie ↥K (.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩) →
      K.index = 3 → IsReeType X 1)
    (k : Sec7Core4 G) (h5 : 5 ≤ k.p → k.KIDExcluded ∧ k.Step75) {H : Subgroup G}
    (hH : k.Config H)
    (hrows3 : k.p = 3 → ∃ P : Subgroup (QuotK7 k.p H),
      Gls3ConclusionPlus (QuotK7 k.p H) (CFSG.generalizedFitting (QuotK7 k.p H)) P ∧
        ∀ m : ℕ, ¬ IsoLie ↥(CFSG.generalizedFitting (QuotK7 k.p H)) (.reeG2 m)) :
    CFSG.Open.genFittingFStar (QuotK7 k.p H) ≤ ImageModK k.p H (Opp k.p H) ∧
      R72Shape k.p (LKQuot7 k.p H) := by
  refine ⟨genFittingFStar_le_imageModK k hH, ?_⟩
  have h35 : k.p = 3 ∨ 5 ≤ k.p := by
    have h2 := k.prime.two_le
    have hne := k.odd
    by_cases h4 : k.p = 4
    · rcases k.prime.eq_one_or_self_of_dvd 2 ⟨2, by omega⟩ with h | h <;> omega
    · omega
  rcases h35 with h3 | hp5
  · obtain ⟨P, hG, hRee⟩ := hrows3 h3
    exact r72Shape_three hR3 (hbr .M11) k h3 hH hG hRee
  · obtain ⟨hno, h75⟩ := h5 hp5
    exact r72Shape_five hId hLie hCyc hOutP hbr k hp5 hno h75 hH

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
