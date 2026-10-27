module

public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeNarrow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.LieType.SeitzGeneration.OuterModel

public section

open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP CFSG.AGLEmbeddingD2
open CFSG.RankThree.PartOne.Census3 (IsoLie)

namespace CFSG.RankThree.PartTwo.Sec19

@[expose] def TrialityThreeInner : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K],
    IsoLie K (.trialityD4 q) → ∀ E : Subgroup (MulAut K), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
        Subgroup.closure (fixUnion E) = ⊤

@[expose] def TrialityThreeOuter : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K],
    IsoLie K (.trialityD4 q) → ∀ E : Subgroup (MulAut K), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → ¬ (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
        Subgroup.closure (fixUnion E) = ⊤

section Bridge


theorem seitzExcAnisotropicTrialityThreeTwo_of_inner (h : TrialityThreeInner) :
    SeitzExcAnisotropicTrialityThreeTwo := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, ⟨q, rfl⟩, ⟨rfl, hch⟩, -, -⟩
  have hqp : q.p = 2 := by
    have h := hch
    change (TauCeti.LieTypeIndex.trialityD4 q).characteristic = 2 at h
    rwa [TauCeti.LieTypeIndex.characteristic_trialityD4] at h
  have hfs := finite_isSimpleGroup_cat_trialityD4 hv
  haveI : Finite (Cat ⟨.trialityD4 q, hv⟩) := hfs.1
  haveI : IsSimpleGroup (Cat ⟨.trialityD4 q, hv⟩) := hfs.2
  have hel := isElementaryAbelian_of_isElemAbelian hE
  rw [planeGen_iff_closure_fixUnion]
  exact h q hqp _ ⟨hv, ⟨MulEquiv.refl _⟩⟩ E hel hc
    (fun φ hφ => (hin hφ).imp fun g hg => hg.symm)

theorem seitzThreeTrialityWideTwo_of_outer (h : TrialityThreeOuter) :
    SeitzThreeTrialityWideTwo := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨rfl, ⟨q, rfl⟩, hch, hcase⟩
  have hqp : q.p = 2 := by
    have h := hch
    change (TauCeti.LieTypeIndex.trialityD4 q).characteristic = 2 at h
    rwa [TauCeti.LieTypeIndex.characteristic_trialityD4] at h
  have hfs := finite_isSimpleGroup_cat_trialityD4 hv
  haveI : Finite (Cat ⟨.trialityD4 q, hv⟩) := hfs.1
  haveI : IsSimpleGroup (Cat ⟨.trialityD4 q, hv⟩) := hfs.2
  have hel := isElementaryAbelian_of_isElemAbelian hE
  have hr2 : RankLE2 3 (Cat ⟨.trialityD4 q, hv⟩) :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv (by omega)
  rcases hcase with ⟨hout, -⟩ | ⟨-, hnr⟩
  · rw [planeGen_iff_closure_fixUnion]
    exact h q hqp _ ⟨hv, ⟨MulEquiv.refl _⟩⟩ E hel hc
      (fun hall => hout fun φ hφ => (hall φ hφ).elim fun g hg => ⟨g, hg.symm⟩)
  · exact absurd hr2 hnr

end Bridge

end CFSG.RankThree.PartTwo.Sec19
