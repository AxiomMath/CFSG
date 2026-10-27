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

@[expose] def KSL3Span : Prop :=
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
        closure {w : W | ∃ k ∈ Kstar, ∃ x : W, w = x⁻¹ * (k • x)} = ⊤ ∧
        ∀ P' : Subgroup ↥H, normalizer ((S : Subgroup ↥H) : Set ↥H) ≤ P' → IsCoatom P' →
          P' ≠ Pℓ →
          closure (⋃ k ∈ Kstar,
            k • ((closure (⋃ p ∈ P', p • (ℓ : Set W)) : Subgroup W) : Set W)) = ⊤

@[expose] def KSL3Line : Prop :=
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
        ∀ P' : Subgroup ↥H, normalizer ((S : Subgroup ↥H) : Set ↥H) ≤ P' → IsCoatom P' →
          P' ≠ Pℓ →
          let π : Subgroup W := closure (⋃ p ∈ P', p • (ℓ : Set W))
          (∀ w ∈ π, ∃ p ∈ P', w ∈ p • (ℓ : Set W)) ∧
            ∀ s ∈ (S : Subgroup ↥H), ∀ w ∈ π, w⁻¹ * (s • w) ∈ ℓ

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
