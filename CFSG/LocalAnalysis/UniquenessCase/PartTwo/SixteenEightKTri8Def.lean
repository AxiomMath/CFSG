module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def S16kTwistIso {K : Type} [Field K] [Finite K]
    (a b : MulAut ↥(StatedOmega (StatedQuadPlus 4 K))) : Prop :=
  ∃ T : Multiplicative (Fin 4 ⊕ Fin 4 → K) ≃* Multiplicative (Fin 4 ⊕ Fin 4 → K),
    ∀ (x : ↥(StatedOmega (StatedQuadPlus 4 K))) (v : Multiplicative (Fin 4 ⊕ Fin 4 → K)),
      T (natAct (StatedOmega (StatedQuadPlus 4 K)) (a x) v) =
        natAct (StatedOmega (StatedQuadPlus 4 K)) (b x) (T v)

@[expose] def S16kOmega8OutInner : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ (α θ : MulAut ↥(StatedOmega (StatedQuadPlus 4 K))),
      S16kTwistIso 1 α → S16kTwistIso 1 (θ * α * θ⁻¹) → ¬ S16kTwistIso 1 θ →
        ∃ g : ↥(StatedOmega (StatedQuadPlus 4 K)), ∀ x, α x = g * x * g⁻¹

variable {G : Type} [Group G] [Finite G]

structure S16kTri8Cfg (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
    (I₁ I₂ : Subgroup (Vtil V₀ V hV))
    (π₁ : ↥(StatedOmega (StatedQuadPlus 4 K₁)) →* ↥(lBar V₀ V hV L))
    (π₂ : ↥(StatedOmega (StatedQuadPlus 4 K₂)) →* ↥(lBar V₀ V hV L)) : Prop where
  card₁ : Nat.card K₁ = 2
  card₂ : Nat.card K₂ = 2
  le₁ : fixV (lBar V₀ V hV L) ≤ I₁
  le₂ : fixV (lBar V₀ V hV L) ≤ I₂
  ind₁ : I₁ ⊓ (fixV (lBar V₀ V hV L) ⊔ I₂) ≤ fixV (lBar V₀ V hV L)
  ind₂ : I₂ ⊓ (fixV (lBar V₀ V hV L) ⊔ I₁) ≤ fixV (lBar V₀ V hV L)
  sup : fixV (lBar V₀ V hV L) ⊔ (I₁ ⊔ I₂) = ⊤
  real₁ : (FFModel.nat (StatedOmega (StatedQuadPlus 4 K₁))).RealizesVia (lBar V₀ V hV L) I₁
    (fixV (lBar V₀ V hV L)) π₁
  real₂ : (FFModel.nat (StatedOmega (StatedQuadPlus 4 K₂))).RealizesVia (lBar V₀ V hV L) I₂
    (fixV (lBar V₀ V hV L)) π₂
  ne : ¬ S16kModelsEquivVia (FFModel.nat (StatedOmega (StatedQuadPlus 4 K₁)))
    (FFModel.nat (StatedOmega (StatedQuadPlus 4 K₁))).act
    (FFModel.nat (StatedOmega (StatedQuadPlus 4 K₂))) π₁ π₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
