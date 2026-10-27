module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.OfCore
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Setup4Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (QuotK7 IsReeType)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree (Gls3ConclusionPlus)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]


theorem r72_dataOfSetup4_of (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hOutP : CFSG.AGLEmbedding.KFactSmallOutPPrime)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hR3 : ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
      Subgroup.centralizer (K : Set X) = ⊥ → IsoLie ↥K (.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩) →
      K.index = 3 → IsReeType X 1)
    (hSE : StronglyEmbeddedFive) (hB : BadNoStrongThree)
    (hrows3 : ∀ (k : Sec7Core4 G) {H : Subgroup G}, k.Config H → k.p = 3 →
      ∃ P : Subgroup (QuotK7 k.p H),
        Gls3ConclusionPlus (QuotK7 k.p H) (CFSG.generalizedFitting (QuotK7 k.p H)) P ∧
          ∀ m : ℕ, ¬ IsoLie ↥(CFSG.generalizedFitting (QuotK7 k.p H)) (.reeG2 m))
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F07.R72
      (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) := by
  intro p H h7
  let k := setup4Core hS hU S hPart p h7.1 h7.2.1 h7.2.2.1
  have hH : k.Config H := config_of_sec7Hyp k h7 rfl
  exact r72_of_core hId hLie hCyc hOutP hbr hR3 k
    (fun hp5 => ⟨kIDExcluded_of_setup4 hU S hMS hB k rfl hp5, k.step75 hp5 hSE⟩) hH (hrows3 k hH)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
