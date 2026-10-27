module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise

@[expose] def KSL3Geom14 : Prop :=
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
          (∀ Y : Subgroup ↥H, (S : Subgroup ↥H) ≤ Y → Y ≠ ⊤ → Y ≤ Pℓ ∨ Y ≤ P') ∧
          (∀ h : ↥H, (∀ w ∈ π, (h : MulAut W) w = w) → h ^ 2 = 1) ∧
          ∀ x₁ x₂ : ↥H, ℓ.map (x₁ : MulAut W).toMonoidHom ≠ ℓ.map (x₂ : MulAut W).toMonoidHom →
            ∃ y : ↥H, ℓ.map (x₁ : MulAut W).toMonoidHom ⊔ ℓ.map (x₂ : MulAut W).toMonoidHom =
              π.map (y : MulAut W).toMonoidHom

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
