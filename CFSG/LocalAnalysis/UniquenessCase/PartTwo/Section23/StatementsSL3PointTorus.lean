module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def KSL3PointTorus : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    IsSLn ↥H 3 n → CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n → 3 ≤ n →
      letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
      letI : MulAction ↥H W := MulAction.compHom W H.subtype
      letI : MulAction ↥H (Set W) := Set.mulActionSet
      ∀ S : Sylow 2 ↥H,
        letI : MulDistribMulAction ↥S W :=
          MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
        let ℓ : Subgroup W := fixedPointSubgroup ↥S W
        let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
        let Kstar : Subgroup ↥H := Hinf Pℓ
        ∀ g : ↥H, Odd (orderOf g) → g ^ 3 ≠ 1 →
          (∀ k ∈ Kstar, g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 Kstar) →
          (∀ w : W, g • w = w → w = 1) ∧
          (∀ u ∈ CFSG.Open.pCoreOf 2 Kstar, g * u * g⁻¹ = u → u = 1)

end CFSG.LocalAnalysis.UniquenessCase.UC22
