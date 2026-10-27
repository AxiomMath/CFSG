module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.GGQ2Frame

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQTwoClLabel (lab : LargeEvenLabel) : Prop :=
  lab.n < 2 ∧ (lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C)

@[expose] def GGQTwoClFrameIn {K₀ : Type} [Group K₀] (E : Subgroup K₀) (t : ℕ) : Prop :=
  ∃ coord : Additive ↥E ≃+ PlaneRaw.V t,
    (ggAutomizer (⊤ : Subgroup K₀) E).map (ggLin (p := 3) coord) = PlaneRaw.signedPermGroup t ∧
      ∀ (v : ↥E) (i₁ : Fin t), v ≠ 1 → (∀ i, i ≠ i₁ → coord (Additive.ofMul v) i = 0) →
        ∀ X : Subgroup K₀, IsComponentOf X (Subgroup.centralizer ({(v : K₀)} : Set K₀)) →
          (∃ i, PlaneRaw.negEquiv t i ∈ (ggAutomizer X E).map (ggLin (p := 3) coord)) ∨
            ∃ i j, i ≠ j ∧ PlaneRaw.rotEquiv t i j ∈ (ggAutomizer X E).map (ggLin (p := 3) coord)

@[expose] def GGQTwoClLocal {G : Type} [Group G] (Bs K : Subgroup G) : Prop :=
  ∃ (t : ℕ) (Φ : (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) →* MulAut ↥Bs),
    3 ≤ t ∧ Function.Injective Φ ∧
    ggAutomizer K Bs = (PlaneRaw.signedPermGroup t).map Φ ∧
    (∀ i, GGIsReflection 3 (Φ (PlaneRaw.negEquiv t i))) ∧
    (∀ i j, i ≠ j → GGIsReflection 3 (Φ (PlaneRaw.swapEquiv t i j))) ∧
    (∀ v : ↥Bs, (∀ i, Φ (PlaneRaw.negEquiv t i) v = v) →
      (v : G) ∈ Subgroup.centralizer (K : Set G)) ∧
    ∀ (v : ↥Bs) (i₁ : Fin t), v ≠ 1 → Φ (PlaneRaw.negEquiv t i₁) v = v⁻¹ →
      ∀ X : Subgroup G, IsComponentOf X (K ⊓ Subgroup.centralizer ({(v : G)} : Set G)) →
        (∃ i, Φ (PlaneRaw.negEquiv t i) ∈ ggAutomizer X Bs) ∨
          ∃ i j, i ≠ j ∧ Φ (PlaneRaw.rotEquiv t i j) ∈ ggAutomizer X Bs

end CFSG.StandardType

end
