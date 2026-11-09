module

public import Mathlib.Data.List.Dedup
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnumInputs

public section

namespace CFSG.KD.L5.Fast

open CFSG.GH74.GLS.C3.Layer2.Model

inductive KT where
  | leaf : KT
  | node : Nat → KT → KT → KT

@[expose] def KT.mem (x : Nat) : KT → Bool
  | .leaf => false
  | .node k l r => cond (Nat.blt x k) (l.mem x) (cond (Nat.blt k x) (r.mem x) true)

@[expose] def KT.ins (y : Nat) : KT → KT
  | .leaf => .node y .leaf .leaf
  | .node k l r =>
    cond (Nat.blt y k) (.node k (l.ins y) r)
      (cond (Nat.blt k y) (.node k l (r.ins y)) (.node k l r))

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp e) h

theorem KT.mem_ins (x y : Nat) : ∀ t : KT, (t.ins y).mem x = (x == y || t.mem x)
  | .leaf => by
    simp only [KT.ins, KT.mem]
    rcases Nat.lt_trichotomy x y with h | h | h
    · simp [Nat.blt_eq.mpr h, Nat.ne_of_lt h]
    · subst h; simp
    · simp [Nat.blt_eq.mpr h, Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]
  | .node k l r => by
    have il := KT.mem_ins x y l
    have ir := KT.mem_ins x y r
    rcases Nat.lt_trichotomy y k with hy | hy | hy
    · have e1 : Nat.blt y k = true := Nat.blt_eq.mpr hy
      simp only [KT.ins, e1, Bool.cond_true, KT.mem, il]
      rcases Nat.lt_trichotomy x k with hx | hx | hx
      · simp [Nat.blt_eq.mpr hx]
      · subst hx; simp [Nat.ne_of_gt hy]
      · simp [Nat.blt_eq.mpr hx, Nat.not_lt.mpr (Nat.le_of_lt hx), show x ≠ y by omega]
    · subst hy
      have e : KT.ins y (KT.node y l r) = KT.node y l r := by
        simp only [KT.ins, blt_false (Nat.lt_irrefl y), Bool.cond_false]
      rw [e]
      by_cases hx : x = y
      · subst hx
        simp only [KT.mem, blt_false (Nat.lt_irrefl x), Bool.cond_false, beq_self_eq_true,
          Bool.true_or]
      · simp [hx]
    · have e1 : Nat.blt y k = false := blt_false (by omega)
      have e2 : Nat.blt k y = true := Nat.blt_eq.mpr hy
      simp only [KT.ins, e1, e2, Bool.cond_true, Bool.cond_false, KT.mem, ir]
      rcases Nat.lt_trichotomy x k with hx | hx | hx
      · simp [Nat.blt_eq.mpr hx, show x ≠ y by omega]
      · subst hx; simp [Nat.ne_of_lt hy]
      · simp [Nat.blt_eq.mpr hx, Nat.not_lt.mpr (Nat.le_of_lt hx)]

@[expose] def dedupK {α : Type*} (key : α → Nat) : List α → List α × KT
  | [] => ([], .leaf)
  | a :: l =>
    let r := dedupK key l
    cond (r.2.mem (key a)) r (a :: r.1, r.2.ins (key a))

theorem dedupK_spec {α : Type*} [DecidableEq α] {key : α → Nat} (hk : Function.Injective key) :
    ∀ l : List α, (dedupK key l).1 = l.dedup ∧
      ∀ x, (dedupK key l).2.mem (key x) = decide (x ∈ l)
  | [] => ⟨rfl, fun x => by simp [dedupK, KT.mem]⟩
  | a :: l => by
    obtain ⟨h1, h2⟩ := dedupK_spec hk l
    by_cases ha : a ∈ l
    · have e : (dedupK key l).2.mem (key a) = true := by rw [h2]; simp [ha]
      simp only [dedupK, e, Bool.cond_true]
      refine ⟨by rw [h1, List.dedup_cons_of_mem ha], fun x => ?_⟩
      rw [h2]
      by_cases hx : x = a
      · subst hx; simp [ha]
      · simp [hx]
    · have e : (dedupK key l).2.mem (key a) = false := by rw [h2]; simp [ha]
      simp only [dedupK, e, Bool.cond_false]
      refine ⟨by rw [h1, List.dedup_cons_of_notMem ha], fun x => ?_⟩
      rw [KT.mem_ins, h2]
      by_cases hx : x = a
      · subst hx; simp
      · have : key x ≠ key a := fun h => hx (hk h)
        simp [hx, this]

@[expose] def closureStepK {G : Type*} [Mul G] (key : G → Nat) (gens : List G) (l : List G) :
    List G :=
  (dedupK key (l ++ l.flatMap fun g => gens.map (g * ·))).1

theorem closureStepK_eq {G : Type*} [Mul G] [DecidableEq G] {key : G → Nat}
    (hk : Function.Injective key) (gens : List G) : closureStepK key gens = closureStep gens := by
  funext l
  exact (dedupK_spec hk _).1

theorem closureList_eq_K {G : Type*} [Mul G] [One G] [DecidableEq G] {key : G → Nat}
    (hk : Function.Injective key) (gens : List G) (k : ℕ) :
    closureList gens k = (closureStepK key gens)^[k] [1] := by
  rw [closureList, closureStepK_eq hk]

end CFSG.KD.L5.Fast

end
