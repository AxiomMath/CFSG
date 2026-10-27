module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight73YInput
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35Holds
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SzFiveTrans
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

theorem stronglyEmbeddedCentralFree_of_kFacts
    (hG3 : CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeSylowCenterTorus)
    (hId : CFSG.AGLEmbedding.KFactSmallIdent) (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hMcL : CFSG.AGLEmbeddingD2.D2HeisLocalAt (.sporadic .McL) fun q => q = 5)
    (hJ4 : CFSG.AGLEmbeddingD2.D2HeisLocalAt (.sporadic .J4) fun q => q = 11)
    (hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      CFSG.AGLEmbeddingD2.D2TransLocalAt (.lie d) fun q => q = 5)
    (hTits : ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal],
      centralizer (K : Set Y) = ⊥ → CFSG.AGLEmbedding.IsTitsGroup ↥K →
        ∀ R : Sylow 5 Y, CFSG.AGLEmbeddingD2.TorusLocal 5 (R : Subgroup Y))
    (hFi : ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → CFSG.AGLEmbedding.IsFi22 L →
      ¬ 5 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) ∧
        ¬ 5 ^ 3 ∣ Nat.card L) :
    StronglyEmbeddedCentralFree := by
  intro p hp hp2 X _ _ hX hO h2 N hN P x hxP hx
  have hp3 : 3 ≤ p := by
    have h2p := hp.two_le
    omega
  by_cases h3 : p = 3
  · subst p
    exact KIZ.eq_one_of_three_of_gls3 hG3 hRee hX hO h2 hN P hxP hx
  · have hp5 : 5 ≤ p := by
      by_contra h5
      have hle : p ≤ 4 := by omega
      interval_cases p
      · exact h3 rfl
      · norm_num at hp
    exact KIZ.eq_one_of_five_le_of_kFacts hId hLie hCyc hMcL hJ4 hSz hTits hFi hp hp5
      hX hO h2 hN P hxP hx

section Holds


theorem stronglyEmbeddedCentralFree_holds
    : StronglyEmbeddedCentralFree :=
  stronglyEmbeddedCentralFree_of_kFacts
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
    CFSG.AGLEmbedding.kFactReeSylowCenterTorus
    CFSG.LocalAnalysis.UniquenessCase.UCK.kFactSmallIdent_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.kFactOneLieIdent_holds
    CFSG.LocalAnalysis.UniquenessCase.UCK.stronglyEmbeddedCyclicOuter_holds
    CFSG.AGLEmbeddingD2.d2HeisLocalAt_mcl
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.d2HeisLocalAt_J4
    (fun d hd => CFSG.AGLEmbeddingD2.d2TransLocalAt_sz32 d hd)
    (fun (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal] hKC hT R =>
      CFSG.AGLEmbeddingD2.torusLocal_tits_sylow hKC
        (CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_tits hT).some R)
    (fun (L : Type) [Group L] [Finite L] hs hL => by
      obtain ⟨e⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_fi22 hs hL
      let hOut : CFSG.ComponentClassification.OuterAutomorphisms.Outer L ≃*
          CFSG.ComponentClassification.OuterAutomorphisms.Outer
            CFSG.Blueprint.NativeSporadic.Fi22 :=
        CFSG.ComponentClassification.OuterAutomorphisms.equivalence e
      let E : CFSG.ComponentClassification.OuterAutomorphisms.Outer L ≃
          CFSG.ComponentClassification.OuterAutomorphisms.Outer
            CFSG.Blueprint.NativeSporadic.Fi22 := hOut.toEquiv
      have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) =
          Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
            CFSG.Blueprint.NativeSporadic.Fi22) :=
        Nat.card_congr E
      constructor
      · rw [hout, CFSG.ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22]
        norm_num
      · rw [CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_of_isFi22 hs hL]
        norm_num)

end Holds

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
