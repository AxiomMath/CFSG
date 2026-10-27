module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants

public import Mathlib.RepresentationTheory.Character

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Auxiliary facts about bundled representations

This file develops character-theoretic and invariant-subspace lemmas for
`Representation k G V`.

Main contents:

* `Representation.character`;
* character formulas for products, tensor products, duals, internal Homs,
  and finite direct sums;
* invariant submodules and the averaging idempotent for finite groups;
* a trace formula for the multiplicity of invariants;
* universe-lifted representations.
-/

section Helper

variable {k : Type*} [CommSemiring k]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable [(i : ι) → AddCommGroup (V i)]
variable [(i : ι) → Module k (V i)]
variable [(i : ι) → Module.Free k (V i)]
variable [(i : ι) → Module.Finite k (V i)]

lemma LinearMap.trace_pi_diag (f : ∀ i, V i →ₗ[k] V i) :
    LinearMap.trace k ((i : ι) → V i)
        (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i)
      =
    ∑ i, LinearMap.trace k (V i) (f i) := by
  classical
  set M' := LinearMap.pi (fun i => f i ∘ₗ LinearMap.proj i)
  convert LinearMap.trace_eq_matrix_trace k
    (Pi.basis fun i => Module.Free.chooseBasis k (V i)) M' using 1
  rw [Finset.sum_congr rfl fun i _ =>
    LinearMap.trace_eq_matrix_trace k
      (Module.Free.chooseBasis k (V i)) (f i)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Pi.basis_apply, Pi.basis_repr]
  rw [Finset.sum_sigma']
  simp_all only [Finset.univ_sigma_univ, pi_apply, coe_comp, coe_proj, Function.comp_apply,
    Function.eval, Pi.single_eq_same, M']

private lemma CFSG.conj_lmap_eq (f : ∀ i, V i →ₗ[k] V i) :
    (DirectSum.linearEquivFunOnFintype k ι V).conj (DirectSum.lmap f) =
    LinearMap.pi (fun i =>
      (f i).comp (LinearMap.proj i)) := by
  exact (Module.dualMap_dualMap_eq_iff k ((i : ι) → V i)).mp rfl

section CommRing

variable {k : Type*} [CommRing k]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable [(i : ι) → AddCommGroup (V i)]
variable [(i : ι) → Module k (V i)]
variable [(i : ι) → Module.Free k (V i)]
variable [(i : ι) → Module.Finite k (V i)]

open DirectSum in
lemma DirectSum.trace_lmap (f : ∀ i, V i →ₗ[k] V i) :
    LinearMap.trace k (⨁ i, V i) (DirectSum.lmap f)
      = ∑ i, LinearMap.trace k (V i) (f i) := by
  rw [← LinearMap.trace_conj' (DirectSum.lmap f) (DirectSum.linearEquivFunOnFintype k ι V)]
  rw [conj_lmap_eq]
  exact LinearMap.trace_pi_diag f

end CommRing

section Group

variable {G k V W : Type*} [Group G] [CommSemiring k] [AddCommGroup V] [Module k V] [AddCommGroup W]
    [Module k W] [Module.Finite k V] [Module.Finite k W] [Module.Free k V]
    (ρ : Representation k G V) (σ : Representation k G W)

/-- dualTensorHom as an equivalence of representations. -/
@[expose, simps!]
noncomputable def Representation.Equiv.dualTensorHomOfFiniteFree :
    Equiv (tprod ρ.dual σ) (linHom ρ σ) where
  toLinearEquiv := dualTensorHomEquiv (R := k) (M := V) (N := W)
  isIntertwining' g := by
    ext v' w v; simp [Module.Dual.transpose_apply]

end Group

end Helper

namespace Representation

variable {G k : Type*} [Monoid G] [Field k]

variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

lemma character_def (ρ : Representation k G V) (g : G) :
  character ρ g = LinearMap.trace k V (ρ g) := rfl

/-- Equivalent representations have the same character. -/
lemma char_equiv
    {ρ : Representation k G V} {σ : Representation k G W}
     (h : Representation.Equiv ρ σ) (g : G) :
    ρ.character g = σ.character g := by
  simp only [character]
  have h_conj : h.toLinearEquiv.conj (ρ g) = σ g := by
    ext v
    change h (ρ g (h.symm v)) = σ g v
    have h' := LinearMap.congr_fun (h.isIntertwining' g) (h.symm v)
    simpa using h'
  rw [← h_conj]
  exact Eq.symm (LinearMap.trace_conj' (ρ g) h.toLinearEquiv)


/-- The character of a product representation is the sum of the characters of
  the two factors. It is named `char_prod_eq_add` because TauCeti's
  `TauCeti.RepresentationTheory.FDRep` declares the pointwise form `Representation.char_prod`;
  two declarations with that name cannot be imported together. -/
@[simp]
lemma char_prod_eq_add [Module.Finite k V] [Module.Finite k W]
  (ρ : Representation k G V) (σ : Representation k G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  ext g
  dsimp[Representation.prod]
  exact LinearMap.trace_prodMap' (ρ g) (σ g)

section directSum

variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable [(i : ι) → AddCommGroup (V i)]
variable [(i : ι) → Module k (V i)]
variable [(i : ι) → Module.Free k (V i)]
variable [(i : ι) → Module.Finite k (V i)]

open DirectSum

/-- The character of a finite direct sum of representations is the sum of the
  characters of the summands. -/
@[simp]
lemma char_directSum (ρ : (i : ι) → Representation k G (V i)) (g : G) :
    (Representation.directSum ρ).character g = ∑ i, (ρ i).character g := by
  dsimp[character]
  exact DirectSum.trace_lmap fun x ↦ (ρ x) g

end directSum

section numOfFixedPoints

variable {k G : Type*} [Monoid G] [CommRing k]

open Classical in
/-- For the permutation representation on `MonoidAlgebra k X`,
    the trace of the linear map attached to `g : G` is the number of fixed points of `g`. -/
lemma ofMulAction_trace
    {X : Type*} [Finite X] [MulAction G X] (g : G) :
    LinearMap.trace k (MonoidAlgebra k X)
        (Representation.ofMulAction k G X g)
      =
    (Nat.card {x : X // g • x = x} : k) := by
  letI : Fintype X := Fintype.ofFinite X
  let b : Module.Basis X k (MonoidAlgebra k X) :=
    (Finsupp.basisSingleOne (R := k) (ι := X)).map
      (MonoidAlgebra.coeffLinearEquiv k).symm
  rw [LinearMap.trace_eq_matrix_trace k b]
  rw [Matrix.trace]
  trans ∑ x : X, if g • x = x then (1 : k) else 0
  · apply Finset.sum_congr rfl
    intro x _
    change
      (LinearMap.toMatrix b b
        (Representation.ofMulAction k G X g)) x x
        =
      if g • x = x then 1 else 0
    rw [LinearMap.toMatrix_apply]
    dsimp [b]
    simp [Finsupp.single_apply]
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]

end numOfFixedPoints

/--
The average of the character of a finite-group representation is the dimension
of its invariant subspace.
-/
theorem average_char_eq_finrank_invariants
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    [Fintype G] [CharZero k]
    {V : Type w}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) :
    ((Fintype.card G : k)⁻¹) *
        (∑ g : G, ρ.character g)
      =
    (Module.finrank k ρ.invariants : k) := by
  haveI : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  have h := ρ.isProj_averageMap.trace
  rw [← h]
  change
    (Fintype.card G : k)⁻¹ *
        ∑ g : G, (LinearMap.trace k V) (ρ g)
      =
    (LinearMap.trace k V) ρ.averageMap
  rw [Representation.averageMap, GroupAlgebra.average]
  simp only [
    MonoidAlgebra.of_apply,
    map_smul,
    map_sum,
    Representation.asAlgebraHom_single,
    one_smul,
    smul_eq_mul,
    invOf_eq_inv
  ]

end Representation
