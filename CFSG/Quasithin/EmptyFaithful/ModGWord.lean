module

public import CFSG.Quasithin.EmptyFaithful.ModGPerm
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs

public section

namespace CFSG.Quasithin.ModG

section Words

variable {G : Type*} [Group G]

@[expose] def ev (ls : List G) (w : List ℕ) : G := (w.map fun l => ls.getD l 1).prod

theorem ev_nil (ls : List G) : ev ls [] = 1 := rfl

theorem ev_cons (ls : List G) (l : ℕ) (w : List ℕ) : ev ls (l :: w) = ls.getD l 1 * ev ls w := by
  simp [ev]

theorem ev_append (ls : List G) (w₁ w₂ : List ℕ) : ev ls (w₁ ++ w₂) = ev ls w₁ * ev ls w₂ := by
  simp [ev]

theorem ev_mem {H : Subgroup G} {ls : List G} (h : ∀ x ∈ ls, x ∈ H) (w : List ℕ) : ev ls w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons l w ih =>
    rw [ev_cons]
    refine H.mul_mem ?_ ih
    by_cases hl : l < ls.length
    · rw [List.getD_eq_getElem _ _ hl]
      exact h _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (not_lt.mp hl)]
      exact H.one_mem

@[expose] def invW (r : ℕ) (w : List ℕ) : List ℕ := (w.map fun l => (l + r) % (2 * r)).reverse

@[expose] def evc (cs : List ℕ) (w : List ℕ) : ℕ :=
  w.foldr (fun l acc => comp (cs.getD l kId) acc) kId

theorem c_ev (c : G → ℕ) (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId)
    (ls : List G) (w : List ℕ) : c (ev ls w) = evc (ls.map c) w := by
  induction w with
  | nil => rw [ev_nil, hone]; rfl
  | cons l w ih =>
    rw [ev_cons, hmul, ih]
    have h := List.getD_map ls 1 (n := l) c
    rw [hone] at h
    simp only [evc, List.foldr_cons]
    rw [← h]

theorem getD_inv_letter {ls : List G} {r : ℕ} (hinv : ∀ l < r, ls.getD (l + r) 1 = (ls.getD l 1)⁻¹)
    {l : ℕ} (hl : l < 2 * r) : ls.getD ((l + r) % (2 * r)) 1 = (ls.getD l 1)⁻¹ := by
  by_cases h : l < r
  · have : (l + r) % (2 * r) = l + r := Nat.mod_eq_of_lt (by omega)
    rw [this]
    exact hinv l h
  · have h2 : (l + r) % (2 * r) = l - r := by
      have : l + r = (l - r) + 2 * r := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    have h3 := hinv (l - r) (by omega)
    have h4 : l - r + r = l := by omega
    rw [h4] at h3
    rw [h3, inv_inv]

theorem ev_invW {ls : List G} {r : ℕ} (hinv : ∀ l < r, ls.getD (l + r) 1 = (ls.getD l 1)⁻¹)
    (w : List ℕ) (hw : ∀ l ∈ w, l < 2 * r) : ev ls (invW r w) = (ev ls w)⁻¹ := by
  induction w with
  | nil => simp [invW, ev_nil]
  | cons l w ih =>
    have hl : l < 2 * r := hw l List.mem_cons_self
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have : invW r (l :: w) = invW r w ++ [(l + r) % (2 * r)] := by simp [invW]
    rw [this, ev_append, ih', ev_cons, getD_inv_letter hinv hl]
    simp [ev]


theorem map_c_ev (c : G → ℕ) (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId)
    (A : List G) (ws : List (List ℕ)) : (ws.map (ev A)).map c = ws.map (evc (A.map c)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [List.map_cons, List.map_cons, List.map_cons, c_ev c hmul hone A w, ih]

theorem map_c_inv_ev (c : G → ℕ) (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId)
    {A : List G} {r : ℕ} (hA : ∀ l < r, A.getD (l + r) 1 = (A.getD l 1)⁻¹)
    (ws : List (List ℕ)) (hw : ∀ w ∈ ws, ∀ l ∈ w, l < 2 * r) :
    (ws.map fun w => (ev A w)⁻¹).map c = ws.map (fun w => evc (A.map c) (invW r w)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ← ev_invW hA w (hw w List.mem_cons_self),
      c_ev c hmul hone A, ih (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw'))]

end Words

attribute [irreducible] evc

end CFSG.Quasithin.ModG
