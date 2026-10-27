module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.StandardType

open Matrix CFSG.LocalAnalysis.ComponentInitial

namespace LID63

variable {K : Type} [Field K] {n d : ℕ}

@[expose] def hperp (h : UnitaryFieldData 2 n K) (R : Submodule K (Fin d → K)) :
    Submodule K (Fin d → K) where
  carrier := {x | ∀ v ∈ R, (h.bar ∘ v) ⬝ᵥ x = 0}
  zero_mem' := fun v _ => dotProduct_zero _
  add_mem' := fun {x y} hx hy v hv => by rw [dotProduct_add, hx v hv, hy v hv, add_zero]
  smul_mem' := fun c x hx v hv => by rw [dotProduct_smul, hx v hv, smul_zero]

theorem mem_hperp {h : UnitaryFieldData 2 n K} {R : Submodule K (Fin d → K)} {x : Fin d → K} :
    x ∈ hperp h R ↔ ∀ v ∈ R, (h.bar ∘ v) ⬝ᵥ x = 0 :=
  Iff.rfl

@[expose] def dotBilin (K : Type) [Field K] (d : ℕ) : LinearMap.BilinForm K (Fin d → K) :=
  LinearMap.mk₂ K (fun x y => x ⬝ᵥ y) (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _) (fun _ _ _ => dotProduct_add _ _ _)
    (fun _ _ _ => dotProduct_smul _ _ _)

theorem dotBilin_apply (x y : Fin d → K) : dotBilin K d x y = x ⬝ᵥ y := rfl

theorem dotBilin_nondegenerate : (dotBilin K d).Nondegenerate := by
  classical
  constructor
  · intro x hx
    funext i
    have := hx (Pi.single i 1)
    simpa [dotBilin_apply] using this
  · intro y hy
    funext i
    have := hy (Pi.single i 1)
    simpa [dotBilin_apply] using this

@[expose] noncomputable def barPerm (h : UnitaryFieldData 2 n K) : Equiv.Perm (Fin d → K) :=
  Function.Involutive.toPerm (fun x => h.bar ∘ x) (fun x => by
    funext i
    simp [h.bar_bar])

theorem barPerm_apply (h : UnitaryFieldData 2 n K) (x : Fin d → K) :
    barPerm h x = h.bar ∘ x := rfl

theorem dotProduct_bar (h : UnitaryFieldData 2 n K) (v x : Fin d → K) :
    v ⬝ᵥ (h.bar ∘ x) = h.bar ((h.bar ∘ v) ⬝ᵥ x) := by
  unfold dotProduct
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [h.bar_bar]

theorem mem_hperp_iff (h : UnitaryFieldData 2 n K) (R : Submodule K (Fin d → K))
    (x : Fin d → K) : x ∈ hperp h R ↔ barPerm h x ∈ (dotBilin K d).orthogonal R := by
  rw [mem_hperp, LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun v hv => ?_
  rw [dotBilin_apply, barPerm_apply, dotProduct_bar, map_eq_zero_iff _ h.bar.injective]

theorem finrank_hperp [Finite K] (h : UnitaryFieldData 2 n K) (R : Submodule K (Fin d → K)) :
    Module.finrank K (hperp h R) + Module.finrank K R = d := by
  have hB := LinearMap.BilinForm.finrank_orthogonal (dotBilin_nondegenerate (K := K) (d := d)) R
  rw [Module.finrank_fin_fun] at hB
  have hle : Module.finrank K R ≤ d := by
    simpa using Submodule.finrank_le R
  have hcard : Nat.card (hperp h R) = Nat.card ((dotBilin K d).orthogonal R) :=
    Nat.card_congr (Equiv.subtypeEquiv (barPerm h) (mem_hperp_iff h R))
  rw [Module.natCard_eq_pow_finrank (K := K) (V := hperp h R),
    Module.natCard_eq_pow_finrank (K := K) (V := (dotBilin K d).orthogonal R)] at hcard
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have := Nat.pow_right_injective (Nat.succ_le_of_lt hK) hcard
  omega

theorem two_mul_finrank_le [Finite K] (h : UnitaryFieldData 2 n K) {R : Submodule K (Fin d → K)}
    (hR : ∀ u ∈ R, ∀ v ∈ R, (h.bar ∘ v) ⬝ᵥ u = 0) : 2 * Module.finrank K R ≤ d := by
  have h1 : R ≤ hperp h R := fun u hu v hv => hR u hu v hv
  have h2 := Submodule.finrank_mono h1
  have h3 := finrank_hperp h R
  omega

theorem hperp_eq_of_isotropic [Finite K] (h : UnitaryFieldData 2 n K) {R : Submodule K (Fin d → K)}
    (hR : ∀ u ∈ R, ∀ v ∈ R, (h.bar ∘ v) ⬝ᵥ u = 0) (hd : d = 2 * Module.finrank K R) :
    hperp h R = R := by
  have h1 : R ≤ hperp h R := fun u hu v hv => hR u hu v hv
  have h3 := finrank_hperp h R
  exact (Submodule.eq_of_le_of_finrank_le h1 (by omega)).symm

end LID63

end CFSG.StandardType

end
