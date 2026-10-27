module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Reflection
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

public section

namespace CFSG.StandardType.QTwoD6

open Module CFSG.StandardType.QTwoLin

abbrev V7 : Type := Fin 7 → ZMod 3

@[expose] def cartanD6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, -1, 0, 0, 0, 0; -1, 2, -1, 0, 0, 0; 0, -1, 2, -1, 0, 0;
     0, 0, -1, 2, -1, -1; 0, 0, 0, -1, 2, 0; 0, 0, 0, -1, 0, 2]

theorem cartanD6_eq : cartanD6 = CartanMatrix.D 6 := by
  decide +kernel

@[expose] def hvec (i : Fin 6) : V7 := Pi.single i.succ 1

@[expose] def avec (j : Fin 6) : Dual (ZMod 3) V7 :=
  ∑ i : Fin 6, (cartanD6 i j : ZMod 3) • (LinearMap.proj i.succ : V7 →ₗ[ZMod 3] ZMod 3)

theorem avec_hvec (j : Fin 6) : avec j (hvec j) = 2 := by
  classical
  simp only [avec, hvec, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · fin_cases j <;> decide
  · intro i _ hij
    have h : (i.succ : Fin 7) ≠ j.succ := fun hh => hij (Fin.succ_injective 6 hh)
    simp [h]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

@[expose] noncomputable def simpleD6 (j : Fin 6) : V7 ≃ₗ[ZMod 3] V7 := reflection (avec_hvec j)

@[expose] noncomputable def W6 : Subgroup (V7 ≃ₗ[ZMod 3] V7) :=
  Subgroup.closure (Set.range simpleD6)

@[expose] noncomputable def J6 : Subgroup (V7 ≃ₗ[ZMod 3] V7) :=
  Subgroup.closure (simpleD6 '' {j | j ≠ 4})

@[expose] def wb : V7 := ![0, 1, 2, 0, 1, 0, 2]

@[expose] def e0 : V7 := Pi.single 0 1

@[expose] def Dplane : Submodule (ZMod 3) V7 := Submodule.span (ZMod 3) {e0, wb}

@[expose] def swapD6 : Fin 6 ≃ Fin 6 := Equiv.swap 4 5

@[expose] def IsReflLin (g : V7 ≃ₗ[ZMod 3] V7) : Prop :=
  ∃ (c : V7) (φ : Dual (ZMod 3) V7) (h : φ c = 2), g = reflection h

@[expose] def GGQ2D6LinearCell : Prop :=
  ∀ (A : Subgroup (V7 ≃ₗ[ZMod 3] V7)) (ℓ : V7) (Aℓ : Subgroup (V7 ≃ₗ[ZMod 3] V7)),
    TransvectionFree A → W6 ≤ A →
    (∀ φ ∈ A, φ e0 ∈ Submodule.span (ZMod 3) {e0} →
      ∃ w ∈ W6, ∃ c : ZMod 3, c ≠ 0 ∧ ∃ π : Fin 6 ≃ Fin 6, (π = Equiv.refl _ ∨ π = swapD6) ∧
        ∀ i, φ (hvec i) = c • w (hvec (π i))) →
    ℓ ∈ Dplane → ℓ ∉ Submodule.span (ZMod 3) {e0} →
    Aℓ ≤ A → J6 ≤ Aℓ → (∀ φ ∈ Aℓ, φ ℓ = ℓ) → (∃ φ ∈ Aℓ, φ e0 ≠ e0) →
    Aℓ = Subgroup.closure {g | g ∈ Aℓ ∧ IsReflLin g} → 1440 < Nat.card Aℓ →
    ∀ φ ∈ A, φ e0 ∈ Submodule.span (ZMod 3) {e0} →
      ∃ ψ ∈ W6 ⊔ Aℓ, ∀ v ∈ Dplane, ψ (φ v) ∈ Dplane

end CFSG.StandardType.QTwoD6

end
