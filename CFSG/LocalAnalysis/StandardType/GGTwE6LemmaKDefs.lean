module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylMat
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public noncomputable section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open scoped Matrix

@[expose] def sigmaZ3 (Y : Set (Fin 6 → ZMod 3)) : Set (Fin Tag.E6.rank → ℤ) :=
  {α | IsRoot Tag.E6 α ∧ ∀ y ∈ Y, ∑ i : Fin 6, ((α (e6Idx i) : ℤ) : ZMod 3) * y i = 0}

@[expose] def LemmaKCheck : Prop :=
  ∀ Y : AddSubgroup (Fin 6 → ZMod 3), 3 ^ 4 ≤ Nat.card Y →
    ∀ u : WeylGroup Tag.E6, (∀ y ∈ Y, e6WeylMat u *ᵥ y = y) →
      u ∈ Subgroup.closure {s | ∃ α ∈ sigmaZ3 (Y : Set (Fin 6 → ZMod 3)), s = rootReflection α}

end CFSG.StandardType.TwE6LemmaK
