module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Case168_2L4 (D : Data G) (V₀ V : Subgroup G)
    (hV : IsElemAbelian 2 V) (L : Subgroup G) : Prop :=
  IsSym ↥(kBar D.M V₀ V hV L) 3 ∧
    (∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
      IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧
        IsLn ↥L₀ 4 1 ∧ IsLn ↥(lBar V₀ V hV L) 4 1 ∧
        SumOfNat (fun H U Z => BinaryNaturalSL H U Z 4 1) (lStar D.M V₀ V hV L)
          (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2) ∧
    D.sig = {3}

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
