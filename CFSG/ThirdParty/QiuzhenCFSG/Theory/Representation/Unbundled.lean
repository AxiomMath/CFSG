module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Character

namespace CFSG
end CFSG
open CFSG

/-!
# Lightweight unbundled representation API

This file collects the `Representation`-level character and invariant facts
needed by `PFsection1_*`, without importing `FDRep`, `Rep`, or the categorical
character/invariant files.
-/

@[expose] public section

noncomputable section

open MonoidAlgebra
open Module

open scoped BigOperators

namespace CFSG.Theory.Representation

open _root_.Representation

section TracePi

public theorem trace_pi_map_perm {R : Type*} [Field R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {M : Type*} [AddCommGroup M] [Module R M]
    (b : Basis κ R M) (e : ι → ι) (L : ι → M →ₗ[R] M)
    (T : (ι → M) →ₗ[R] (ι → M))
    (hT : ∀ x i, T x i = L i (x (e i))) :
    LinearMap.trace R (ι → M) T =
      ∑ i : ι, if e i = i then LinearMap.trace R M (L i) else 0 := by
  classical
  let B : Basis (Σ _ : ι, κ) R (ι → M) := Pi.basis (fun _ : ι => b)
  rw [LinearMap.trace_eq_matrix_trace R B T]
  simp only [Matrix.trace]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : e i = i
  · rw [if_pos h]
    rw [LinearMap.trace_eq_matrix_trace R b (L i)]
    simp only [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro a ha
    change (LinearMap.toMatrix B B T) ⟨i, a⟩ ⟨i, a⟩ =
      (LinearMap.toMatrix b b (L i)) a a
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    simp [B, hT]
    rw [h]
    simp
  · rw [if_neg h]
    rw [Finset.sum_eq_zero]
    intro a ha
    change (LinearMap.toMatrix B B T) ⟨i, a⟩ ⟨i, a⟩ = 0
    rw [LinearMap.toMatrix_apply]
    have hne : i ≠ e i := fun hi => h hi.symm
    simp [B, hT, hne]


end TracePi

end CFSG.Theory.Representation
