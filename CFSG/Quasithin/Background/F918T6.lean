module

public import CFSG.Quasithin.Background.F918T0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

@[expose] def unitri5 : Subgroup ↥(StatedSL 5 (ZMod 2)) where
  carrier := {g | ∀ i j : Fin 5, j < i → mat g i j = 0}
  one_mem' := fun i j hji => by
    have := (Matrix.blockTriangular_one (b := (id : Fin 5 → Fin 5)) (R := ZMod 2)) hji
    simpa using this
  mul_mem' := fun {a b} ha hb i j hji => by
    have h1 : Matrix.BlockTriangular (mat a) (id : Fin 5 → Fin 5) := fun i j hji => ha i j hji
    have h2 : Matrix.BlockTriangular (mat b) (id : Fin 5 → Fin 5) := fun i j hji => hb i j hji
    have := h1.mul h2 hji
    simpa using this
  inv_mem' := fun {a} ha i j hji => by
    have h1 : Matrix.BlockTriangular (mat a) (id : Fin 5 → Fin 5) := fun i j hji => ha i j hji
    have : Invertible (mat a) := ⟨mat a⁻¹, CFSG.Quasithin.B5.Ln.mat_inv_mul a,
      CFSG.Quasithin.B5.Ln.mat_mul_inv a⟩
    have h3 := Matrix.blockTriangular_inv_of_blockTriangular h1
    have h4 : (mat a)⁻¹ = mat a⁻¹ := Matrix.inv_eq_right_inv (CFSG.Quasithin.B5.Ln.mat_mul_inv a)
    rw [h4] at h3
    exact h3 hji

theorem mem_unitri5 {g : ↥(StatedSL 5 (ZMod 2))} :
    g ∈ unitri5 ↔ ∀ i j : Fin 5, j < i → mat g i j = 0 := Iff.rfl

@[expose] def D35InspExtSqU : Prop :=
  ∀ E : Subgroup ↥(StatedSL 5 (ZMod 2)), E ≤ unitri5 → E ≠ ⊥ → (∀ g ∈ E, ∀ h ∈ E, g * h = h * g) →
    (∀ g ∈ E, g * g = 1) →
    ¬ (2 ^ 10 ≤ Nat.card E *
        Nat.card {B : ↥(altMat 5) //
          ∀ g ∈ E, mat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (mat g)ᵀ = B} ∧
      2 ^ 10 ≤ Nat.card E *
        Nat.card {B : ↥(altMat 5) //
          ∀ g ∈ E, dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B})

end CFSG.Quasithin
