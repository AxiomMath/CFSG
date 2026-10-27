module

public import Mathlib.GroupTheory.Commutator.Basic

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

universe u

/-- The commutator of `H` and `K` is a subgroup of `H ⊔ K`. -/
public lemma CFSG.commutator_le_sup {G : Type u} [Group G] (H K : Subgroup G) : ⁅H, K⁆ ≤ H ⊔ K := by
  refine (Subgroup.commutator_le).2 ?_
  intro h hh k hk
  -- Every commutator `⁅h, k⁆` lies in `H ⊔ K`, hence so does the subgroup they generate.
  have hh' : h ∈ H ⊔ K := Subgroup.mem_sup_left hh
  have hk' : k ∈ H ⊔ K := Subgroup.mem_sup_right hk
  simpa [commutatorElement_def, mul_assoc] using
    (H ⊔ K).mul_mem
      ((H ⊔ K).mul_mem ((H ⊔ K).mul_mem hh' hk') ((H ⊔ K).inv_mem hh'))
      ((H ⊔ K).inv_mem hk')

lemma CFSG.conj_commutator_left {G : Type u} [Group G] (x a b : G) :
    x * ⁅a, b⁆ * x⁻¹ = ⁅x * a, b⁆ * ⁅b, x⁆ := by
  simp [commutatorElement_def, mul_assoc]


-- A small helper: once we control conjugation on a generating set, we control it on the closure.
lemma CFSG.conj_mem_closure {G : Type u} [Group G] {S : Set G} (x y : G) (hy : y ∈ Subgroup.closure S)
    (hS : ∀ z, z ∈ S → x * z * x⁻¹ ∈ Subgroup.closure S) :
    x * y * x⁻¹ ∈ Subgroup.closure S := by
  refine
    Subgroup.closure_induction (k := S)
      (p := fun z _hz => x * z * x⁻¹ ∈ Subgroup.closure S)
      (mem := fun z hz => hS z hz) (one := by simp)
      (mul := ?_) (inv := ?_) hy
  · intro a b _ha _hb ha hb
    simpa [mul_assoc] using (Subgroup.closure S).mul_mem ha hb
  · intro a _ha ha
    simpa [mul_assoc] using (Subgroup.closure S).inv_mem ha

-- Conjugation by elements of the left subgroup preserves the commutator subgroup.
lemma CFSG.conj_mem_commutator_of_mem_left {G : Type u} [Group G] {H' K' : Subgroup G} {x y : G} (hx : x ∈ H')
    (hy : y ∈ ⁅H', K'⁆) : x * y * x⁻¹ ∈ ⁅H', K'⁆ := by
  let S : Set G := {g : G | ∃ a ∈ H', ∃ b ∈ K', ⁅a, b⁆ = g}
  have hy' : y ∈ Subgroup.closure S := by
    simpa [Subgroup.commutator_def, S] using hy
  have hS : ∀ z, z ∈ S → x * z * x⁻¹ ∈ Subgroup.closure S := by
    intro z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    have h₁ : ⁅x * a, b⁆ ∈ Subgroup.closure S := by
      refine Subgroup.subset_closure ?_
      exact ⟨x * a, H'.mul_mem hx ha, b, hb, rfl⟩
    have hxb : ⁅x, b⁆ ∈ Subgroup.closure S := by
      refine Subgroup.subset_closure ?_
      exact ⟨x, hx, b, hb, rfl⟩
    have h₂ : ⁅b, x⁆ ∈ Subgroup.closure S := by
      have : (⁅x, b⁆)⁻¹ ∈ Subgroup.closure S := (Subgroup.closure S).inv_mem hxb
      simpa [commutatorElement_inv] using this
    have : ⁅x * a, b⁆ * ⁅b, x⁆ ∈ Subgroup.closure S := (Subgroup.closure S).mul_mem h₁ h₂
    rewrite [conj_commutator_left]
    exact this
  have : x * y * x⁻¹ ∈ Subgroup.closure S := conj_mem_closure (S := S) x y hy' hS
  simpa [Subgroup.commutator_def, S] using this

/-- The commutator `⁅H, K⁆` is normal in `H ⊔ K`. -/
public theorem CFSG.commutator_normal_in_sup {G : Type u} [Group G] (H K : Subgroup G) :
    ((⁅H, K⁆).subgroupOf (H ⊔ K)).Normal := by

  -- Conjugation by elements of `H` preserves `⁅H, K⁆`.
  have conj_mem_commutator_of_mem_H {x y : G} (hx : x ∈ H) (hy : y ∈ ⁅H, K⁆) :
      x * y * x⁻¹ ∈ ⁅H, K⁆ :=
    conj_mem_commutator_of_mem_left (H' := H) (K' := K) hx hy

  -- Conjugation by elements of `K` preserves `⁅H, K⁆` (reduce to the previous lemma by swapping).
  have conj_mem_commutator_of_mem_K {x y : G} (hx : x ∈ K) (hy : y ∈ ⁅H, K⁆) :
      x * y * x⁻¹ ∈ ⁅H, K⁆ := by
    have hy' : y ∈ ⁅K, H⁆ := by
      simpa [Subgroup.commutator_comm (H₁ := H) (H₂ := K)] using hy
    have h' : x * y * x⁻¹ ∈ ⁅K, H⁆ :=
      conj_mem_commutator_of_mem_left (H' := K) (K' := H) hx hy'
    simpa [Subgroup.commutator_comm (H₁ := K) (H₂ := H)] using h'

  -- First, `⁅H, K⁆ ≤ H ⊔ K`, so we can apply `normal_subgroupOf_iff_le_normalizer`.
  have hcomm_le : ⁅H, K⁆ ≤ H ⊔ K := commutator_le_sup H K

  -- Next, `H ⊔ K ≤ (⁅H, K⁆).normalizer`.
  have hH : H ≤ Subgroup.normalizer (⁅H, K⁆).carrier := by
    intro x hx
    -- Use the normalizer characterization `x ∈ N.normalizer ↔ ∀ n, n ∈ N ↔ x * n * x⁻¹ ∈ N`.
    refine (Subgroup.mem_normalizer_iff (H := ⁅H, K⁆) (g := x)).2 ?_
    intro y
    constructor
    · intro hy
      exact conj_mem_commutator_of_mem_H (x := x) hx hy
    · intro hy
      have hx' : x⁻¹ ∈ H := H.inv_mem hx
      have h : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ ⁅H, K⁆ :=
        conj_mem_commutator_of_mem_H (x := x⁻¹) hx' hy
      simpa [mul_assoc] using h

  have hK : K ≤ Subgroup.normalizer (⁅H, K⁆).carrier := by
    intro x hx
    refine (Subgroup.mem_normalizer_iff (H := ⁅H, K⁆) (g := x)).2 ?_
    intro y
    constructor
    · intro hy
      exact conj_mem_commutator_of_mem_K (x := x) hx hy
    · intro hy
      have hx' : x⁻¹ ∈ K := K.inv_mem hx
      have h : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ ⁅H, K⁆ :=
        conj_mem_commutator_of_mem_K (x := x⁻¹) hx' hy
      simpa [mul_assoc] using h

  have hsup : H ⊔ K ≤ Subgroup.normalizer (⁅H, K⁆).carrier := sup_le hH hK

  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (H := ⁅H, K⁆) (K := H ⊔ K) hcomm_le).mpr hsup
