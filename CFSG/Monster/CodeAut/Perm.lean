module

public import CFSG.Monster.Code.Basis
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Monster.Code

@[expose] def permWord (p : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) : Fin 24 → ZMod 2 :=
  x ∘ ⇑p⁻¹

theorem permWord_apply (p : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) (i : Fin 24) :
    permWord p x (p i) = x i := by
  simp [permWord]

theorem permWord_mul (p q : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) :
    permWord (q * p) x = permWord q (permWord p x) := by
  funext i
  simp [permWord, mul_inv_rev]

@[expose] def AutPerm : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {p | ∀ x : Fin 24 → ZMod 2, x ∈ C ↔ x ∘ ⇑p ∈ C}
  mul_mem' {p q} hp hq x := by
    rw [hp x, hq (x ∘ ⇑p)]
    rfl
  one_mem' x := by
    rfl
  inv_mem' {p} hp x := by
    rw [hp (x ∘ ⇑p⁻¹)]
    simp [Function.comp_assoc]

theorem mem_AutPerm_iff {p : Equiv.Perm (Fin 24)} :
    p ∈ AutPerm ↔ ∀ x : Fin 24 → ZMod 2, x ∈ C ↔ x ∘ ⇑p ∈ C := Iff.rfl

theorem mem_AutPerm_iff_permWord {p : Equiv.Perm (Fin 24)} :
    p ∈ AutPerm ↔ ∀ x : Fin 24 → ZMod 2, x ∈ C ↔ permWord p x ∈ C := by
  rw [← AutPerm.inv_mem_iff]
  rfl

theorem comp_mem_of_mem_AutPerm {p : Equiv.Perm (Fin 24)} (hp : p ∈ AutPerm)
    {x : Fin 24 → ZMod 2} (hx : x ∈ C) : x ∘ ⇑p ∈ C :=
  (hp x).1 hx

theorem permWord_mem_of_mem_AutPerm {p : Equiv.Perm (Fin 24)} (hp : p ∈ AutPerm)
    {x : Fin 24 → ZMod 2} (hx : x ∈ C) : permWord p x ∈ C :=
  (mem_AutPerm_iff_permWord.1 hp x).1 hx

theorem hammingNorm_comp_perm (x : Fin 24 → ZMod 2) (p : Equiv.Perm (Fin 24)) :
    hammingNorm (x ∘ ⇑p) = hammingNorm x := by
  rw [hammingNorm_eq_sum_val, hammingNorm_eq_sum_val]
  exact Equiv.sum_comp p fun i => (x i).val

private theorem comp_mem_of_basis {p : Equiv.Perm (Fin 24)} (h : ∀ i, B i ∘ ⇑p ∈ C)
    {x : Fin 24 → ZMod 2} (hx : x ∈ C) : x ∘ ⇑p ∈ C := by
  rw [eq_comb_of_mem_C hx]
  have e : (∑ i, ψ x i • B i) ∘ ⇑p = ∑ i, ψ x i • (B i ∘ ⇑p) := by
    funext j
    simp [Finset.sum_apply]
  rw [e]
  exact C.sum_mem fun i _ => C.smul_mem _ (h i)

theorem mem_AutPerm_of_basis {p : Equiv.Perm (Fin 24)} (h : ∀ i, B i ∘ ⇑p ∈ C)
    (h' : ∀ i, B i ∘ ⇑p⁻¹ ∈ C) : p ∈ AutPerm := by
  intro x
  refine ⟨comp_mem_of_basis h, fun hx => ?_⟩
  have := comp_mem_of_basis h' hx
  rwa [Function.comp_assoc, show ⇑p ∘ ⇑p⁻¹ = id from by funext i; simp,
    Function.comp_id] at this

end CFSG.Monster.Code
