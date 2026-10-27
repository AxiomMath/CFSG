module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Module.Equiv.Basic

public section

namespace CFSG.StandardType

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private def kappa : Fin 5 → ZMod 3 := ![1, 2, 0, 1, 2]

private def row (i : Fin 5) (a : Fin 5 → ZMod 3) : ZMod 3 :=
  if i = 0 then 2 * a 0 - a 1
  else if i = 1 then -a 0 + 2 * a 1 - a 2
  else if i = 2 then -a 1 + 2 * a 2 - a 3
  else if i = 3 then -a 2 + 2 * a 3 - a 4
  else -a 3 + 2 * a 4

private def S (i : Fin 5) (a : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 :=
  Function.update a i (a i - row i a)

private def Sw : List (Fin 5) → (Fin 5 → ZMod 3) → (Fin 5 → ZMod 3)
  | [], a => a
  | i :: l, a => S i (Sw l a)

private def words : List (List (Fin 5)) :=
  [[4, 2, 0], [3, 4, 2, 3, 0], [4, 1, 2, 0, 1],
   [0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0],
   [3, 1], [2, 3, 4, 3, 0, 1, 2, 0], [1, 2, 3, 4, 0, 1, 2, 3, 1, 2, 0, 1]]

private def ok (a : Fin 5 → ZMod 3) (l : List (Fin 5)) : Bool :=
  let b := Sw l a + a
  b == 0 || b == kappa || b == (2 : ZMod 3) • kappa

private def good (a : Fin 5 → ZMod 3) : Bool :=
  words.any (ok a)

private def good5 (a0 a1 a2 a3 a4 : ZMod 3) : Bool :=
  good ![a0, a1, a2, a3, a4]

private theorem good5_all :
    ∀ a0 a1 a2 a3 a4 : ZMod 3, good5 a0 a1 a2 a3 a4 = true := by
  decide

private theorem good_all (a : Fin 5 → ZMod 3) : good a = true := by
  have hv : (![a 0, a 1, a 2, a 3, a 4] : Fin 5 → ZMod 3) = a := by
    funext i
    fin_cases i <;> simp
  rw [← hv]
  exact good5_all (a 0) (a 1) (a 2) (a 3) (a 4)

private theorem ok_iff (a : Fin 5 → ZMod 3) (l : List (Fin 5)) :
    ok a l = true ↔
      Sw l a + a = 0 ∨ Sw l a + a = kappa ∨
        Sw l a + a = (2 : ZMod 3) • kappa := by
  simp [ok, beq_iff_eq, or_assoc]

private theorem exists_word (a : Fin 5 → ZMod 3) :
    ∃ l ∈ words, Sw l a + a = 0 ∨ Sw l a + a = kappa ∨
      Sw l a + a = (2 : ZMod 3) • kappa := by
  have h := good_all a
  rw [good, List.any_eq_true] at h
  obtain ⟨l, hl, hl'⟩ := h
  exact ⟨l, hl, (ok_iff a l).mp hl'⟩

private noncomputable def E (c : Fin 5 → V) : (Fin 5 → ZMod 3) →ₗ[ZMod 3] V :=
  Fintype.linearCombination (ZMod 3) c

private theorem E_update (c : Fin 5 → V) (a : Fin 5 → ZMod 3) (i : Fin 5) (x : ZMod 3) :
    E c (Function.update a i x) = E c a + (x - a i) • c i := by
  rw [E, Pi.update_eq_sub_add_single, map_add, map_sub,
    Fintype.linearCombination_apply_single, Fintype.linearCombination_apply_single,
    sub_smul]
  abel

private theorem alpha_E (c : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 5 i j : ZMod 3))
    (i : Fin 5) (a : Fin 5 → ZMod 3) :
    α i (E c a) = row i a := by
  rw [E, Fintype.linearCombination_apply]
  rw [map_sum]
  simp only [map_smul, hpair, smul_eq_mul]
  fin_cases i <;> simp [row, Fin.sum_univ_five, CartanMatrix.A] <;> ring

private theorem sE (c : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 5 i j : ZMod 3))
    (s : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i)
    (i : Fin 5) (a : Fin 5 → ZMod 3) :
    s i (E c a) = E c (S i a) := by
  rw [hs, alpha_E c α hpair i a]
  unfold S
  rw [E_update]
  have h : (a i - row i a) - a i = -row i a := by ring
  rw [h, neg_smul]
  abel

private theorem prod_map_E (c : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 5 i j : ZMod 3))
    (s : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) :
    ∀ (l : List (Fin 5)) (a : Fin 5 → ZMod 3),
      (l.map s).prod (E c a) = E c (Sw l a)
  | [], a => by simp [Sw]
  | i :: l, a => by
      rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply,
        prod_map_E c α hpair s hs l a, sE c α hpair s hs i (Sw l a)]
      rfl

private theorem E_kappa (c : Fin 5 → V)
    (hdep : c 0 + (2 : ZMod 3) • c 1 + c 3 + (2 : ZMod 3) • c 4 = 0) :
    E c kappa = 0 := by
  rw [E, Fintype.linearCombination_apply]
  simp [kappa, Fin.sum_univ_five]
  simpa using hdep

private theorem E_kappa_smul (c : Fin 5 → V)
    (hdep : c 0 + (2 : ZMod 3) • c 1 + c 3 + (2 : ZMod 3) • c 4 = 0)
    (k : ZMod 3) : E c (k • kappa) = 0 := by
  rw [map_smul, E_kappa c hdep, smul_zero]

theorem ggQ2TN6_neg (c : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 5 i j : ZMod 3))
    (s : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i)
    (hdep : c 0 + (2 : ZMod 3) • c 1 + c 3 + (2 : ZMod 3) • c 4 = 0) :
    ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      ∃ w ∈ Subgroup.closure (Set.range s), w h = -h := by
  intro h hh
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hh
  have ha' : E c a = h := by
    rw [E, Fintype.linearCombination_apply]
    exact ha
  obtain ⟨l, _hl, hk⟩ := exists_word a
  refine ⟨(l.map s).prod, ?_, ?_⟩
  · exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hx
      exact Subgroup.subset_closure (Set.mem_range_self i)
  · rw [← ha', prod_map_E c α hpair s hs l a]
    have hE : E c (Sw l a) + E c a = 0 := by
      rcases hk with hk | hk | hk
      · rw [← map_add, hk, map_zero]
      · rw [← map_add, hk, E_kappa c hdep]
      · rw [← map_add, hk, E_kappa_smul c hdep (2 : ZMod 3)]
    rw [eq_neg_of_add_eq_zero_left hE, ha']

end CFSG.StandardType

end
