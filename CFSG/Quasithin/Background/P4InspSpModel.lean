module

public import CFSG.Quasithin.Background.P4InspSpBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix

namespace G11

namespace P4InspSp

abbrev Coord : Type := Fin 2 ⊕ Fin 2 → ZMod 2

def vC : Fin 6 → Coord := ![0, Pi.single (Sum.inl 0) 1, Pi.single (Sum.inr 0) 1,
  Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 + Pi.single (Sum.inl 1) 1,
  Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 + Pi.single (Sum.inr 1) 1,
  Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1 + Pi.single (Sum.inl 1) 1 +
    Pi.single (Sum.inr 1) 1]

def Tm : Matrix (Fin 2 ⊕ Fin 2) (Fin 6) (ZMod 2) := Matrix.of fun r i => vC i r

def formC (z w : Coord) : ZMod 2 := z ⬝ᵥ (Matrix.J (Fin 2) (ZMod 2) *ᵥ w)

theorem p4inspsp_Tm_surj :
    ∀ z : Coord, ∃ x : Fin 6 → ZMod 2, ∑ i, x i = 0 ∧ Tm *ᵥ x = z := by decide +kernel

theorem p4inspsp_Tm_ker : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 →
    (Tm *ᵥ x = 0 ↔ (x = 0 ∨ ∀ i, x i = 1)) := by decide +kernel

theorem p4inspsp_Tm_form : ∀ x y : Fin 6 → ZMod 2, ∑ i, x i = 0 → ∑ i, y i = 0 →
    formC (Tm *ᵥ x) (Tm *ᵥ y) = x ⬝ᵥ y := by decide +kernel

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

structure A6Model (f : LinearMap.BilinForm (ZMod 2) U) where
  β : ↥(permCore 6) →ₗ[ZMod 2] U
  surj : Function.Surjective β
  ker : ∀ u : ↥(permCore 6),
    β u = 0 ↔ ((u : Fin 6 → ZMod 2) = 0 ∨ ∀ i, (u : Fin 6 → ZMod 2) i = 1)
  isom : ∀ x y : ↥(permCore 6),
    f (β x) (β y) = (x : Fin 6 → ZMod 2) ⬝ᵥ (y : Fin 6 → ZMod 2)

theorem p4inspsp_exists_model [Finite U] {f : LinearMap.BilinForm (ZMod 2) U}
    (h : IsSymplectic f) (hd : Module.finrank (ZMod 2) U = 4) : Nonempty (A6Model f) := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  obtain ⟨m, b, hm, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis
      f h.1 (p4inspsp_nondeg h)
  have hm2 : m = 2 := by omega
  subst hm2
  let c : U ≃ₗ[ZMod 2] Coord := b.equivFun
  have hform : ∀ x y : U, f x y = formC (c x) (c y) := by
    intro x y
    rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b f x y, hb]
    rfl
  let T : (Fin 6 → ZMod 2) →ₗ[ZMod 2] Coord := Matrix.mulVecLin Tm
  let β : ↥(permCore 6) →ₗ[ZMod 2] U := c.symm.toLinearMap ∘ₗ T ∘ₗ (permCore 6).subtype
  have hβ : ∀ x : ↥(permCore 6), c (β x) = Tm *ᵥ (x : Fin 6 → ZMod 2) := fun x => by
    simp [β, T]
  refine ⟨⟨β, ?_, ?_, ?_⟩⟩
  · intro u
    obtain ⟨x, hx, hTx⟩ := p4inspsp_Tm_surj (c u)
    refine ⟨⟨x, hx⟩, c.injective ?_⟩
    rw [hβ]
    exact hTx
  · intro u
    have hu : ∑ i, (u : Fin 6 → ZMod 2) i = 0 := u.2
    rw [← p4inspsp_Tm_ker _ hu, ← hβ, ← map_zero c]
    exact c.injective.eq_iff.symm
  · intro x y
    have hx : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := x.2
    have hy : ∑ i, (y : Fin 6 → ZMod 2) i = 0 := y.2
    rw [hform, hβ, hβ]
    exact p4inspsp_Tm_form _ _ hx hy

end P4InspSp

end G11

end CFSG.Quasithin
