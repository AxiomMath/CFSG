module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameTau

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

@[expose] def dDot (m : ℕ) : LinearMap.BilinForm (ZMod 3) (DVec m) :=
  LinearMap.mk₂ (ZMod 3) (fun v w => v ⬝ᵥ w) add_dotProduct smul_dotProduct
    dotProduct_add dotProduct_smul

section Inputs


@[expose] def GGQTwoDRMBaseInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∃ hx : x ∈ Bs,
          (GGWeylOfType 3 (CoxeterMatrix.A (m - 1)) (ggAutomizer L Bs) ∨
            GGWeylOfType 3 (ggCoxeterMatrixD (m - 1)) (ggAutomizer L Bs)) ∧
          ∀ a ∈ ggAutomizer L Bs, a ⟨x, hx⟩ = ⟨x, hx⟩

@[expose] def GGQTwoDRMBaseInput : Prop :=
  GGQTwoDRMBaseInputOn fun m => 7 ≤ m

@[expose] def GGQTwoDRMStabInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        ∀ (hx : x ∈ Bs) (β : Additive ↥Bs ≃+ DVec m),
          (∀ (t : Fin m) (s : ↥Bs),
            β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) :
                MulAut ↥Bs)) s)) =
              dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
                (β (Additive.ofMul s))) →
          Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} ≤
              2 ^ (m - 1) * (m - 1).factorial ∧
          ∀ a ∈ ggInduced ⊤ Bs, GGIsReflection 3 a → a ⟨x, hx⟩ = ⟨x, hx⟩ →
            a ∈ ggAutomizer L Bs ∨
              ∃ i : Fin m, ∀ b : ↥Bs, β (Additive.ofMul (a b)) = dNeg m i (β (Additive.ofMul b))

@[expose] def GGQTwoDRMStabInput : Prop :=
  GGQTwoDRMStabInputOn fun m => 7 ≤ m

end Inputs

end CFSG.StandardType.QTwo

end
