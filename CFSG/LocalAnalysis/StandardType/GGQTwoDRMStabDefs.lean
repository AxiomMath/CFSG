module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

@[expose] def dEvenStab (m : ℕ) (v : DVec m) : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m) where
  carrier := {g | g ∈ dEven m ∧ g v = v}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    change a (b v) = v
    rw [hb.2, ha.2]⟩
  one_mem' := ⟨one_mem _, rfl⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
    have h := congrArg (⇑a⁻¹) ha.2
    rw [← LinearEquiv.mul_apply, inv_mul_cancel] at h
    exact h.symm⟩

@[expose] def dIsRefl {m : ℕ} (g : DVec m ≃ₗ[ZMod 3] DVec m) : Prop :=
  ∃ (c : DVec m) (f : Module.Dual (ZMod 3) (DVec m)), f c = 2 ∧ ∀ v, g v = v - f v • c

@[expose] def qtwoDActsAs {G : Type} [Group G] {Bs : Subgroup G} {m : ℕ}
    (β : Additive ↥Bs ≃+ DVec m) (A : Subgroup (MulAut ↥Bs))
    (W : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m)) : Prop :=
  (∀ a ∈ A, ∃ w ∈ W, ∀ s : ↥Bs, β (Additive.ofMul (a s)) = w (β (Additive.ofMul s))) ∧
    ∀ w ∈ W, ∃ a ∈ A, ∀ s : ↥Bs, β (Additive.ofMul (a s)) = w (β (Additive.ofMul s))

section Inputs


@[expose] def GGQTwoDRMBaseCoordInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), 7 ≤ m → M = (ggCoxeterMatrixD m).reindex e' →
        ∃ (hx : x ∈ Bs) (β₀ : Additive ↥Bs ≃+ DVec m),
          qtwoDActsAs β₀ (ggAutomizerJoin L Bs 𝒦) (dEven m) ∧
            ((∃ ε : DVec m, (∀ i, ε i = 1 ∨ ε i = -1) ∧
                β₀ (Additive.ofMul ⟨x, hx⟩) = ε ∧
                qtwoDActsAs β₀ (ggAutomizer L Bs) (dEvenStab m ε)) ∨
              ∃ (i₀ : Fin m) (c : ZMod 3), c ≠ 0 ∧
                β₀ (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1 ∧
                qtwoDActsAs β₀ (ggAutomizer L Bs) (dEvenStab m (Pi.single i₀ 1)))

end Inputs

end CFSG.StandardType.QTwo

end
