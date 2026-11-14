module

public import Mathlib.LinearAlgebra.Projectivization.Action

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module

variable (k F : Type*) [Field k] [Field F] [Algebra k F]

abbrev scalarHom : Fˣ →* (F ≃ₗ[k] F) := DistribMulAction.toModuleAut k F

@[expose] def scalars : Subgroup (F ≃ₗ[k] F) := (scalarHom k F).range

variable {k F}

theorem scalarHom_apply (c : Fˣ) (x : F) : scalarHom k F c x = c * x := rfl

theorem scalarHom_mem_scalars (c : Fˣ) : scalarHom k F c ∈ scalars k F := ⟨c, rfl⟩

theorem mem_scalars {g : F ≃ₗ[k] F} : g ∈ scalars k F ↔ ∃ c : Fˣ, scalarHom k F c = g :=
  Iff.rfl

theorem scalarHom_injective : Function.Injective (scalarHom k F) := by
  intro c d h
  have := LinearEquiv.congr_fun h 1
  rw [scalarHom_apply, scalarHom_apply, mul_one, mul_one] at this
  exact Units.ext this

theorem mk_eq_mk_of_eq {V : Type*} [AddCommGroup V] [Module k V] {v w : V} (hv : v ≠ 0)
    (hw : w ≠ 0) (h : v = w) : mk k v hv = mk k w hw := by
  subst h
  rfl

theorem units_smul_mk (c : Fˣ) {x : F} (hx : x ≠ 0) :
    c • mk k x hx = mk k (c * x) (mul_ne_zero c.ne_zero hx) :=
  rfl

theorem scalarHom_smul (c : Fˣ) (p : ℙ k F) : scalarHom k F c • p = c • p := by
  induction p using Projectivization.ind with
  | h x hx => rfl

theorem scalarHom_smul_set (c : Fˣ) (s : Set (ℙ k F)) : scalarHom k F c • s = c • s := by
  ext q
  simp only [Set.mem_smul_set, scalarHom_smul]

theorem units_smul_eq_self_iff {c : Fˣ} {p : ℙ k F} :
    c • p = p ↔ (c : F) ∈ Set.range (algebraMap k F) := by
  induction p using Projectivization.ind with
  | h x hx =>
    rw [units_smul_mk, mk_eq_mk_iff']
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [Algebra.smul_def] at ha
      exact mul_right_cancel₀ hx ha
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [Algebra.smul_def, ha]⟩

theorem exists_units_smul_eq (p q : ℙ k F) : ∃ c : Fˣ, c • p = q := by
  induction p using Projectivization.ind with
  | h x hx =>
    induction q using Projectivization.ind with
    | h y hy =>
      refine ⟨Units.mk0 (y * x⁻¹) (mul_ne_zero hy (inv_ne_zero hx)), ?_⟩
      rw [units_smul_mk]
      exact mk_eq_mk_of_eq _ _ (by rw [Units.val_mk0, mul_assoc, inv_mul_cancel₀ hx, mul_one])

theorem exists_eq_algebraMap_of_forall_smul_eq {g : F ≃ₗ[k] F} (hg : ∀ p : ℙ k F, g • p = p) :
    ∃ c : k, c ≠ 0 ∧ ∀ x, g x = algebraMap k F c * x := by
  have key : ∀ x : F, x ≠ 0 → ∃ a : k, a • x = g x := by
    intro x hx
    have h := hg (mk k x hx)
    rwa [smul_mk, mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := key 1 one_ne_zero
  have hgx : ∀ x, g x = algebraMap k F a * x := by
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    by_cases hspan : x ∈ Submodule.span k ({1} : Set F)
    · obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hspan
      calc g x = g (d • (1 : F)) := by rw [hd]
        _ = d • g 1 := by rw [map_smul]
        _ = d • (a • (1 : F)) := by rw [ha]
        _ = a • (d • (1 : F)) := by rw [smul_comm]
        _ = a • x := by rw [hd]
        _ = algebraMap k F a * x := Algebra.smul_def a x
    · have hidx : LinearIndependent k ![x, (1 : F)] := by
        rw [linearIndependent_fin2]
        exact ⟨one_ne_zero, fun b hb => hspan (Submodule.mem_span_singleton.mpr ⟨b, hb⟩)⟩
      have hx1 : x + 1 ≠ 0 := by
        intro h
        have hxneg : x = -1 := by linear_combination h
        exact hspan (Submodule.mem_span_singleton.mpr ⟨-1, by rw [neg_one_smul, hxneg]⟩)
      obtain ⟨b, hb⟩ := key x hx
      obtain ⟨e, he⟩ := key (x + 1) hx1
      have hEq : b • x + a • (1 : F) = e • x + e • (1 : F) := by
        have h1 : e • (x + 1) = g x + g 1 := by rw [he, map_add]
        rw [smul_add] at h1
        rw [h1, hb, ha]
      have hzero : (b - e) • x + (a - e) • (1 : F) = 0 := by
        have h2 : (b - e) • x + (a - e) • (1 : F)
            = (b • x + a • (1 : F)) - (e • x + e • (1 : F)) := by
          rw [sub_smul, sub_smul]
          abel
        rw [h2, hEq, sub_self]
      obtain ⟨hbe, hae⟩ := (LinearIndependent.pair_iff).mp hidx (b - e) (a - e) hzero
      have hba : b = a := by
        rw [sub_eq_zero] at hbe hae
        rw [hbe, hae]
      rw [← hb, hba, Algebra.smul_def]
  refine ⟨a, fun ha0 => ?_, hgx⟩
  have h1 := hgx 1
  rw [ha0, map_zero, zero_mul] at h1
  exact one_ne_zero (g.injective (h1.trans g.map_zero.symm))

theorem exists_algEquiv_of_normalizes [FiniteDimensional k F] (l : IntermediateField k F)
    (g : F ≃ₗ[k] F) (hg : ∀ a ∈ l, ∃ a' ∈ l, ∀ x, g (a * x) = a' * g x) :
    ∃ σ : l ≃ₐ[k] l, ∀ (a : l) (x : F), g (a * x) = σ a * g x := by
  have hg1 : g 1 ≠ 0 := fun h => one_ne_zero (g.injective (h.trans g.map_zero.symm))
  have hval : ∀ a ∈ l, ∀ a' : F, (∀ x, g (a * x) = a' * g x) → a' = g a * (g 1)⁻¹ := by
    intro a _ a' ha'
    have := ha' 1
    rw [mul_one] at this
    rw [this, mul_assoc, mul_inv_cancel₀ hg1, mul_one]
  have hmem : ∀ a ∈ l, g a * (g 1)⁻¹ ∈ l := by
    intro a ha
    obtain ⟨a', ha'l, ha'⟩ := hg a ha
    rw [← hval a ha a' ha']
    exact ha'l
  have hform : ∀ a ∈ l, ∀ x, g (a * x) = g a * (g 1)⁻¹ * g x := by
    intro a ha x
    obtain ⟨a', -, ha'⟩ := hg a ha
    rw [← hval a ha a' ha']
    exact ha' x
  let φ : l →ₐ[k] l :=
    { toFun := fun a => ⟨g a * (g 1)⁻¹, hmem a a.2⟩
      map_one' := Subtype.ext (by
        change g 1 * (g 1)⁻¹ = 1
        exact mul_inv_cancel₀ hg1)
      map_mul' := fun a b => Subtype.ext (by
        change g (a * b) * (g 1)⁻¹ = g a * (g 1)⁻¹ * (g b * (g 1)⁻¹)
        rw [hform a a.2, mul_assoc, mul_assoc])
      map_zero' := Subtype.ext (by
        change g 0 * (g 1)⁻¹ = 0
        rw [map_zero, zero_mul])
      map_add' := fun a b => Subtype.ext (by
        change g (a + b) * (g 1)⁻¹ = g a * (g 1)⁻¹ + g b * (g 1)⁻¹
        rw [map_add, add_mul])
      commutes' := fun c => Subtype.ext (by
        change g (algebraMap k F c) * (g 1)⁻¹ = algebraMap k F c
        have h : g (algebraMap k F c) = algebraMap k F c * g 1 := by
          conv_lhs => rw [Algebra.algebraMap_eq_smul_one c, map_smul, Algebra.smul_def]
        rw [h, mul_assoc, mul_inv_cancel₀ hg1, mul_one]) }
  refine ⟨AlgEquiv.ofBijective φ (AlgHom.bijective φ), fun a x => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  exact hform a a.2 x

end CFSG.ShultStronglyClosedTI.Singer
