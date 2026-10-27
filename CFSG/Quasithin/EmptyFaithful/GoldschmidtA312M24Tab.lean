
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base
public import CFSG.Quasithin.Background.A312SporGen
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Blueprint CFSG.Sporadic.Mathieu
open scoped Pointwise

abbrev G24 : Type := ↥NativeSporadic.M24

section Tab

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem tab_one_L : tab n (1 : Γ) = List.range n := by
  have h := tab_one_toArray (Γ := Γ) (n := n)
  have := congrArg Array.toList h
  simpa [idTab] using this

theorem eq_of_tab_eq [FaithfulSMul Γ (Fin n)] {x y : Γ} (h : tab n x = tab n y) : x = y := by
  have hxy : ∀ b < n, act n x b = act n y b := fun b _ => by unfold act; rw [h]
  have h1 : x⁻¹ * y = 1 := by
    apply base_of_faithful (n := n)
    intro b hb
    have hbn := List.mem_range.mp hb
    rw [act_mul _ _ hbn, ← hxy b hbn, ← act_mul _ _ hbn, inv_mul_cancel, act_one hbn]
  calc x = x * (x⁻¹ * y) := by rw [h1, mul_one]
    _ = y := by group

theorem tab_injective [FaithfulSMul Γ (Fin n)] : Function.Injective (tab (Γ := Γ) n) :=
  fun _ _ h => eq_of_tab_eq h

theorem comm_of_tab [FaithfulSMul Γ (Fin n)] {x y : Γ}
    (h : compTab (tab n x) (tab n y) = compTab (tab n y) (tab n x)) : x * y = y * x := by
  apply eq_of_tab_eq (n := n)
  rw [tab_mul, tab_mul]
  exact h

@[expose] def evalEltL (els : List Γ) (w : List ℕ) : Γ := (w.map fun l => els.getD l 1).prod

@[expose] def wordTab (n : ℕ) (tabs : List (List ℕ)) : List ℕ → List ℕ
  | [] => List.range n
  | l :: w => compTab (tabs.getD l []) (wordTab n tabs w)

theorem evalEltL_cons (els : List Γ) (l : ℕ) (w : List ℕ) :
    evalEltL els (l :: w) = els.getD l 1 * evalEltL els w := by
  simp [evalEltL]

theorem tab_evalEltL (els : List Γ) (w : List ℕ) (hw : ∀ l ∈ w, l < els.length) :
    tab n (evalEltL els w) = wordTab n (els.map (tab n)) w := by
  induction w with
  | nil => simp [evalEltL, wordTab, tab_one_L]
  | cons l w ih =>
    have hl : l < els.length := hw l List.mem_cons_self
    rw [evalEltL_cons, tab_mul, ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')), wordTab]
    congr 1
    rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by simpa using hl)]
    simp

@[expose] def powTabL (n : ℕ) (t : List ℕ) : ℕ → List ℕ
  | 0 => List.range n
  | k + 1 => compTab t (powTabL n t k)

theorem tab_pow_L (g : Γ) (k : ℕ) : tab n (g ^ k) = powTabL n (tab n g) k := by
  induction k with
  | zero => simp [powTabL, tab_one_L]
  | succ k ih => rw [pow_succ', tab_mul, ih, powTabL]

theorem evalEltL_mem {H : Subgroup Γ} (els : List Γ) (hels : ∀ x ∈ els, x ∈ H) (w : List ℕ) :
    evalEltL els w ∈ H := by
  unfold evalEltL
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
  by_cases hl : l < els.length
  · rw [List.getD_eq_getElem _ _ hl]
    exact hels _ (List.getElem_mem hl)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact H.one_mem

end Tab

end CFSG.Quasithin.A312M24
