module

public import CFSG.Quasithin.EmptyFaithful.A38c5FmDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.A38c5.Fm

open Equiv

private def affXor (x y : Fin 8) : Fin 8 := Fin.ofNat 8 (x.val ^^^ y.val)

private def Aff8 : Subgroup P8 where
  carrier := {g | ∀ x y z, g (affXor (affXor x y) z) = affXor (affXor (g x) (g y)) (g z)}
  mul_mem' := by
    intro g h hg hh x y z
    simp only [Equiv.Perm.mul_apply, hh x y z, hg (h x) (h y) (h z)]
  one_mem' := fun _ _ _ => rfl
  inv_mem' := by
    intro g hg x y z
    apply g.injective
    rw [perm_apply_inv, hg]
    simp only [perm_apply_inv]

private theorem aff_of_add {g : P8} (h : ∀ x y, g (affXor x y) = affXor (g x) (g y)) :
    g ∈ Aff8 :=
  fun x y z => by rw [h, h]

private theorem aff_xor_self (x : Fin 8) : affXor x x = 0 := by
  revert x; decide

private def affTrans (t : Fin 8) : P8 where
  toFun x := affXor x t
  invFun x := affXor x t
  left_inv x := by revert t x; decide
  right_inv x := by revert t x; decide

private theorem affTrans_mem_Smu (t : Fin 8) : affTrans t ∈ Smu := by
  show ∀ x, affTrans t (partner x) = partner (affTrans t x)
  revert t; decide

private theorem affTrans_mem_Aff8 (t : Fin 8) : affTrans t ∈ Aff8 := by
  show ∀ x y z, affTrans t (affXor (affXor x y) z) =
    affXor (affXor (affTrans t x) (affTrans t y)) (affTrans t z)
  revert t; decide

private theorem affTrans_even (t : Fin 8) : affTrans t ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  revert t; decide +kernel

private theorem aff_cls (x y : Fin 8) (h : x.val / 2 = y.val / 2) : y = x ∨ y = partner x := by
  revert x y; decide

private theorem aff_partner_div (x : Fin 8) : (partner x).val / 2 = x.val / 2 := by
  revert x; decide

private theorem aff_cls_ne {g : P8} (hg : g ∈ Smu) {x y : Fin 8} (h : x.val / 2 ≠ y.val / 2) :
    (g x).val / 2 ≠ (g y).val / 2 := by
  intro e
  have hg' : ∀ x, g (partner x) = partner (g x) := hg
  rcases aff_cls _ _ e with h1 | h1
  · exact h (by rw [g.injective h1])
  · rw [← hg' x] at h1
    exact h (by rw [g.injective h1, aff_partner_div])

private abbrev affValid (a b c d : Fin 8) : Prop :=
  a.val / 2 ≠ b.val / 2 ∧ a.val / 2 ≠ c.val / 2 ∧ a.val / 2 ≠ d.val / 2 ∧
  b.val / 2 ≠ c.val / 2 ∧ b.val / 2 ≠ d.val / 2 ∧ c.val / 2 ≠ d.val / 2

private theorem aff_valid_of_smu {g : P8} (hg : g ∈ Smu) : affValid (g 0) (g 2) (g 4) (g 6) :=
  ⟨aff_cls_ne hg (by decide), aff_cls_ne hg (by decide), aff_cls_ne hg (by decide),
    aff_cls_ne hg (by decide), aff_cls_ne hg (by decide), aff_cls_ne hg (by decide)⟩

private def affV (a b c d : Fin 8) : Fin 8 → Fin 8 :=
  ![a, partner a, b, partner b, c, partner c, d, partner d]

private theorem eq_affV (g : P8) (hg : g ∈ Smu) : ⇑g = affV (g 0) (g 2) (g 4) (g 6) := by
  have h : ∀ x, g (partner x) = partner (g x) := hg
  funext x
  fin_cases x
  · rfl
  · exact h 0
  · rfl
  · exact h 2
  · rfl
  · exact h 4
  · rfl
  · exact h 6

set_option maxRecDepth 100000 in
private theorem aff_core : ∀ b c d : Fin 8, affValid 0 b c d →
    ∀ h : Function.Bijective (affV 0 b c d), Equiv.Perm.sign (Equiv.ofBijective _ h) = 1 →
    ∀ x y, affV 0 b c d (affXor x y) = affXor (affV 0 b c d x) (affV 0 b c d y) := by
  decide +kernel

private theorem aff_of_fix_zero {g : P8} (hA : g ∈ alternatingGroup (Fin 8)) (hS : g ∈ Smu)
    (h0 : g 0 = 0) : g ∈ Aff8 := by
  have hv := aff_valid_of_smu hS
  have hf := eq_affV g hS
  rw [h0] at hv hf
  have hb : Function.Bijective (affV 0 (g 2) (g 4) (g 6)) := hf ▸ g.bijective
  have he : Equiv.ofBijective _ hb = g := Equiv.ext fun x => (congrFun hf x).symm
  have hs : Equiv.Perm.sign (Equiv.ofBijective _ hb) = 1 := by
    rw [he]; exact Equiv.Perm.mem_alternatingGroup.1 hA
  exact aff_of_add fun x y => by rw [hf]; exact aff_core _ _ _ hv hb hs x y

private theorem aff_inf_le : alternatingGroup (Fin 8) ⊓ Smu ≤ Aff8 := by
  rintro g ⟨hA, hS⟩
  have h0 : (affTrans (g 0) * g) 0 = 0 := aff_xor_self (g 0)
  have h1 := aff_of_fix_zero (mul_mem (affTrans_even _) hA) (mul_mem (affTrans_mem_Smu _) hS) h0
  simpa using mul_mem (inv_mem (affTrans_mem_Aff8 (g 0))) h1

private def affCycle012 : P8 := swap 0 1 * swap 1 2

private def affCycle024 : P8 := swap 0 2 * swap 2 4

private def affSwap1256 : P8 := swap 1 2 * swap 5 6

private theorem affCycle012_even : affCycle012 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [affCycle012]

private theorem affCycle024_even : affCycle024 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [affCycle024]

private theorem affSwap1256_even : affSwap1256 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [affSwap1256]

private theorem affCycle012_not_Aff8 : affCycle012 ∉ Aff8 := by
  intro h
  have h1 : ∀ x y z, affCycle012 (affXor (affXor x y) z) =
      affXor (affXor (affCycle012 x) (affCycle012 y)) (affCycle012 z) := h
  revert h1
  decide

private theorem affSwap1256_mem_Aff8 : affSwap1256 ∈ Aff8 := by
  show ∀ x y z, affSwap1256 (affXor (affXor x y) z) =
    affXor (affXor (affSwap1256 x) (affSwap1256 y)) (affSwap1256 z)
  decide

private theorem affSwap1256_not_Smu : affSwap1256 ∉ Smu := by
  intro h
  have h1 : ∀ x, affSwap1256 (partner x) = partner (affSwap1256 x) := h
  revert h1
  decide

private theorem affCycle024_not_PStab {B : Finset (Fin 8)} (hB : B ∈ blocks3) :
    affCycle024 ∉ PStab B := by
  intro h
  have h1 : (∀ x, affCycle024 x ∈ B ↔ x ∈ B) ∨ (∀ x, affCycle024 x ∈ B ↔ x ∉ B) := h
  simp only [blocks3, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl <;> revert h1 <;> decide

theorem kB_ne_alt {B : Finset (Fin 8)} (hB : B ∈ blocks3) :
    alternatingGroup (Fin 8) ⊓ PStab B ≠ alternatingGroup (Fin 8) := by
  intro h
  have h1 : affCycle024 ∈ alternatingGroup (Fin 8) ⊓ PStab B := by
    rw [h]; exact affCycle024_even
  exact affCycle024_not_PStab hB h1.2

theorem kmu_not_coatom :
    ∃ H : Subgroup P8, H ≤ alternatingGroup (Fin 8) ∧ H ≠ alternatingGroup (Fin 8) ∧
      alternatingGroup (Fin 8) ⊓ Smu < H := by
  refine ⟨alternatingGroup (Fin 8) ⊓ Aff8, inf_le_left, fun h => ?_, ?_⟩
  · have h1 : affCycle012 ∈ alternatingGroup (Fin 8) ⊓ Aff8 := by
      rw [h]; exact affCycle012_even
    exact affCycle012_not_Aff8 h1.2
  · refine lt_of_le_of_ne (le_inf inf_le_left aff_inf_le) fun h => ?_
    have h1 : affSwap1256 ∈ alternatingGroup (Fin 8) ⊓ Smu := by
      rw [h]; exact ⟨affSwap1256_even, affSwap1256_mem_Aff8⟩
    exact affSwap1256_not_Smu h1.2

end CFSG.Quasithin.A38c5.Fm
