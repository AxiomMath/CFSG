module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.SzR1

variable {P : Type*} [Group P] {Ω : Type*}

structure GramRel (z : P) (w : Ω → P) : Prop where
  z_sq : z * z = 1
  z_comm : ∀ g : P, g * z = z * g
  w_sq : ∀ i, w i * w i = 1
  w_comm : ∀ i j, i ≠ j → w i * w j = z * (w j * w i)

@[expose] def gprod (w : Ω → P) (l : List Ω) : P := (l.map w).prod

@[simp] theorem gprod_nil (w : Ω → P) : gprod w [] = 1 := rfl

@[simp] theorem gprod_cons (w : Ω → P) (i : Ω) (l : List Ω) :
    gprod w (i :: l) = w i * gprod w l := by
  simp [gprod]

theorem gprod_append (w : Ω → P) (l l' : List Ω) :
    gprod w (l ++ l') = gprod w l * gprod w l' := by
  simp [gprod]

theorem countP_ne_add_count [DecidableEq Ω] (j : Ω) (l : List Ω) :
    l.countP (fun i => decide (i ≠ j)) + l.count j = l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases hij : i = j
    · subst hij
      simp at ih ⊢
      omega
    · simp [hij] at ih ⊢
      omega

theorem choose_two_succ (n : ℕ) : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
  have h := Nat.choose_succ_succ' n 1
  norm_num [Nat.choose_one_right] at h
  omega

namespace GramRel

variable {z : P} {w : Ω → P}

theorem mul_zpow_comm (h : GramRel z w) (g : P) (n : ℕ) : g * z ^ n = z ^ n * g :=
  (Commute.pow_right (show Commute g z from h.z_comm g) n).eq

theorem z_pow_add_self (h : GramRel z w) (a : ℕ) : z ^ (a + a) = 1 := by
  rw [← two_mul, pow_mul, pow_two, h.z_sq, one_pow]

theorem z_inv (h : GramRel z w) : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq

theorem w_inv (h : GramRel z w) (i : Ω) : (w i)⁻¹ = w i := inv_eq_of_mul_eq_one_right (h.w_sq i)

theorem z_pow_eq_one_iff (h : GramRel z w) (hz : z ≠ 1) (n : ℕ) : z ^ n = 1 ↔ Even n := by
  constructor
  · intro hn
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨k, rfl⟩ := hodd
    have : z ^ (2 * k + 1) = z := by
      rw [pow_succ, pow_mul, pow_two, h.z_sq, one_pow, one_mul]
    exact hz (this ▸ hn)
  · rintro ⟨k, rfl⟩
    exact h.z_pow_add_self k

section Prod

variable (h : GramRel z w)
include h

theorem gprod_inv (l : List Ω) : (gprod w l)⁻¹ = gprod w l.reverse := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [gprod_cons, mul_inv_rev, ih, h.w_inv, List.reverse_cons, gprod_append, gprod_cons,
      gprod_nil, mul_one]

theorem gprod_perm {l l' : List Ω} (hp : l.Perm l') :
    ∃ k : ℕ, gprod w l = z ^ k * gprod w l' := by
  induction hp with
  | nil => exact ⟨0, by simp⟩
  | cons i _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k, ?_⟩
    rw [gprod_cons, gprod_cons, hk, ← mul_assoc, ← mul_assoc, h.mul_zpow_comm (w i) k]
  | swap i j l =>
    by_cases hij : i = j
    · subst hij
      exact ⟨0, by simp⟩
    · refine ⟨1, ?_⟩
      rw [gprod_cons, gprod_cons, gprod_cons, gprod_cons, ← mul_assoc, h.w_comm j i (Ne.symm hij),
        pow_one, mul_assoc, mul_assoc]
  | trans _ _ ih1 ih2 =>
    obtain ⟨k1, hk1⟩ := ih1
    obtain ⟨k2, hk2⟩ := ih2
    refine ⟨k1 + k2, ?_⟩
    rw [hk1, hk2, ← mul_assoc, pow_add]

theorem gprod_cons_cons (i : Ω) (l : List Ω) : gprod w (i :: i :: l) = gprod w l := by
  rw [gprod_cons, gprod_cons, ← mul_assoc, h.w_sq, one_mul]

theorem mul_gprod [DecidableEq Ω] (j : Ω) (l : List Ω) :
    w j * gprod w l = z ^ (l.countP (fun i => decide (i ≠ j))) * (gprod w l * w j) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases hij : i = j
    · subst hij
      have hc : (i :: l).countP (fun k => decide (k ≠ i)) =
          l.countP (fun k => decide (k ≠ i)) := by
        simp
      rw [hc, gprod_cons, ← mul_assoc, h.w_sq, one_mul, ih]
      calc gprod w l = z ^ (l.countP (fun k => decide (k ≠ i)) +
            l.countP (fun k => decide (k ≠ i))) * gprod w l := by
            rw [h.z_pow_add_self, one_mul]
        _ = _ := by
            simp only [pow_add, mul_assoc, h.w_sq, mul_one]
    · have hc : (i :: l).countP (fun k => decide (k ≠ j)) =
          l.countP (fun k => decide (k ≠ j)) + 1 := by
        simp [hij]
      rw [hc, gprod_cons, ← mul_assoc, h.w_comm j i (Ne.symm hij), mul_assoc z,
        mul_assoc (w i) (w j), ih, ← mul_assoc (w i), h.mul_zpow_comm (w i), pow_succ']
      simp only [mul_assoc]

theorem mem_closure_iff {x : P} :
    x ∈ Subgroup.closure (insert z (Set.range w)) ↔
      ∃ (a : ℕ) (l : List Ω), x = z ^ a * gprod w l := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | ⟨i, rfl⟩
      · exact ⟨1, [], by simp⟩
      · exact ⟨0, [i], by simp⟩
    | one => exact ⟨0, [], by simp⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, l, rfl⟩ := ihx
      obtain ⟨b, l', rfl⟩ := ihy
      refine ⟨a + b, l ++ l', ?_⟩
      calc z ^ a * gprod w l * (z ^ b * gprod w l')
          = z ^ a * (gprod w l * z ^ b) * gprod w l' := by simp only [mul_assoc]
        _ = z ^ a * (z ^ b * gprod w l) * gprod w l' := by rw [h.mul_zpow_comm (gprod w l) b]
        _ = z ^ (a + b) * gprod w (l ++ l') := by
            rw [gprod_append, pow_add]
            simp only [mul_assoc]
    | inv x _ ihx =>
      obtain ⟨a, l, rfl⟩ := ihx
      refine ⟨a, l.reverse, ?_⟩
      rw [mul_inv_rev, h.gprod_inv, ← inv_pow, h.z_inv, h.mul_zpow_comm]
  · rintro ⟨a, l, rfl⟩
    refine Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) a) ?_
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [gprod_cons]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)) ih

theorem gprod_sq [DecidableEq Ω] {l : List Ω} (hl : l.Nodup) :
    gprod w l * gprod w l = z ^ (Nat.choose l.length 2) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hnd := List.nodup_cons.mp hl
    have h1 := h.mul_gprod i l
    have hc : l.countP (fun k => decide (k ≠ i)) = l.length := by
      have := countP_ne_add_count i l
      rw [List.count_eq_zero_of_not_mem hnd.1] at this
      omega
    rw [hc] at h1
    rw [List.length_cons, choose_two_succ, pow_add, gprod_cons]
    calc w i * gprod w l * (w i * gprod w l)
        = (w i * gprod w l) * w i * gprod w l := by simp only [mul_assoc]
      _ = (z ^ l.length * (gprod w l * w i)) * w i * gprod w l := by rw [h1]
      _ = z ^ l.length * (gprod w l * (w i * w i)) * gprod w l := by simp only [mul_assoc]
      _ = z ^ l.length * (gprod w l * gprod w l) := by
          rw [h.w_sq, mul_one]
          simp only [mul_assoc]
      _ = z ^ l.length * z ^ (Nat.choose l.length 2) := by rw [ih hnd.2]
      _ = z ^ (Nat.choose l.length 2) * z ^ l.length := by
          rw [← pow_add, ← pow_add, add_comm]

theorem even_countP_of_central [DecidableEq Ω] (hz : z ≠ 1) {x : P} {a : ℕ} {l : List Ω}
    (hx : x = z ^ a * gprod w l) (hc : ∀ i, x * w i = w i * x) (j : Ω) :
    Even (l.countP (fun i => decide (i ≠ j))) := by
  have h1 := hc j
  rw [hx] at h1
  have h2 := h.mul_gprod j l
  have h3 : z ^ a * (gprod w l * w j) =
      z ^ a * (z ^ (l.countP (fun i => decide (i ≠ j))) * (gprod w l * w j)) := by
    calc z ^ a * (gprod w l * w j) = z ^ a * gprod w l * w j := (mul_assoc _ _ _).symm
      _ = w j * (z ^ a * gprod w l) := h1
      _ = z ^ a * (w j * gprod w l) := by
          calc w j * (z ^ a * gprod w l) = (w j * z ^ a) * gprod w l := (mul_assoc _ _ _).symm
            _ = (z ^ a * w j) * gprod w l := by rw [h.mul_zpow_comm (w j) a]
            _ = z ^ a * (w j * gprod w l) := mul_assoc _ _ _
      _ = _ := by rw [h2]
  have h4 := mul_left_cancel h3
  have h5 : z ^ (l.countP (fun i => decide (i ≠ j))) = 1 := by
    have h6 : 1 * (gprod w l * w j) =
        z ^ (l.countP (fun i => decide (i ≠ j))) * (gprod w l * w j) := by
      rwa [one_mul]
    exact (mul_right_cancel h6).symm
  exact (h.z_pow_eq_one_iff hz _).mp h5

theorem central_mem [DecidableEq Ω] (hz : z ≠ 1) (l₀ : List Ω) (hl₀ : l₀.Nodup)
    (hall : ∀ i, i ∈ l₀) {x : P} (hc : ∀ i, x * w i = w i * x) :
    ∀ (n a : ℕ) (l : List Ω), l.length = n → x = z ^ a * gprod w l →
      (∃ b : ℕ, x = z ^ b) ∨ (∃ b : ℕ, x = z ^ b * gprod w l₀) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a l hn hx
    by_cases hnd : l.Nodup
    · by_cases hl : l = []
      · left
        exact ⟨a, by simpa [hl] using hx⟩
      · obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil l hl
        have hev : ∀ j, Even (l.countP (fun i => decide (i ≠ j))) :=
          fun j => h.even_countP_of_central hz hx hc j
        have hcnt : l.countP (fun i => decide (i ≠ j)) + 1 = l.length := by
          have := countP_ne_add_count j l
          rwa [List.count_eq_one_of_mem hnd hj] at this
        have hall' : ∀ i, i ∈ l := by
          intro i
          by_contra hi
          have h1 := hev i
          have h2 := hev j
          have h3 : l.countP (fun k => decide (k ≠ i)) = l.length := by
            have := countP_ne_add_count i l
            rw [List.count_eq_zero_of_not_mem hi] at this
            omega
          rw [h3] at h1
          obtain ⟨r, hr⟩ := h1
          obtain ⟨s, hs⟩ := h2
          omega
        have hperm : l.Perm l₀ := List.perm_of_nodup_nodup_toFinset_eq hnd hl₀ (by
          ext i
          simp [hall i, hall' i])
        obtain ⟨k, hk⟩ := h.gprod_perm hperm
        right
        refine ⟨a + k, ?_⟩
        rw [hx, hk, pow_add, mul_assoc]
    · rw [List.nodup_iff_count_le_one] at hnd
      push Not at hnd
      obtain ⟨i, hi⟩ := hnd
      have hmem : i ∈ l := List.count_pos_iff.mp (by omega)
      have p1 : l.Perm (i :: l.erase i) := List.perm_cons_erase hmem
      have hcnt' : 0 < (l.erase i).count i := by
        rw [List.count_erase_self]
        omega
      have hmem' : i ∈ l.erase i := List.count_pos_iff.mp hcnt'
      have p2 : (l.erase i).Perm (i :: (l.erase i).erase i) := List.perm_cons_erase hmem'
      have p3 : l.Perm (i :: i :: (l.erase i).erase i) := p1.trans (List.Perm.cons i p2)
      obtain ⟨k, hk⟩ := h.gprod_perm p3
      rw [h.gprod_cons_cons] at hk
      have hlen : ((l.erase i).erase i).length < n := by
        rw [List.length_erase_of_mem hmem', List.length_erase_of_mem hmem]
        have : 0 < l.length := List.length_pos_of_mem hmem
        omega
      exact ih _ hlen (a + k) ((l.erase i).erase i) rfl (by rw [hx, hk, pow_add, mul_assoc])

theorem central_mem_closure [DecidableEq Ω] (hz : z ≠ 1) (l₀ : List Ω) (hl₀ : l₀.Nodup)
    (hall : ∀ i, i ∈ l₀) {x : P} (hx : x ∈ Subgroup.closure (insert z (Set.range w)))
    (hc : ∀ i, x * w i = w i * x) :
    (∃ b : ℕ, x = z ^ b) ∨ (∃ b : ℕ, x = z ^ b * gprod w l₀) := by
  obtain ⟨a, l, hx'⟩ := h.mem_closure_iff.mp hx
  exact h.central_mem hz l₀ hl₀ hall hc _ a l rfl hx'

theorem commute_gprod_univ [Fintype Ω] [DecidableEq Ω] (hodd : Odd (Fintype.card Ω))
    (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀) (j : Ω) :
    w j * gprod w l₀ = gprod w l₀ * w j := by
  have hlen : l₀.length = Fintype.card Ω := by
    have : l₀.toFinset = Finset.univ := by
      ext i
      simp [hall i]
    rw [← List.toFinset_card_of_nodup hl₀, this, Finset.card_univ]
  have h1 := h.mul_gprod j l₀
  have h2 := countP_ne_add_count j l₀
  rw [List.count_eq_one_of_mem hl₀ (hall j)] at h2
  obtain ⟨r, hr⟩ := hodd
  have h3 : l₀.countP (fun i => decide (i ≠ j)) = r + r := by omega
  rw [h3, h.z_pow_add_self, one_mul] at h1
  exact h1

theorem commute_gprod_univ_closure [Fintype Ω] [DecidableEq Ω] (hodd : Odd (Fintype.card Ω))
    (l₀ : List Ω) (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀) {x : P}
    (hx : x ∈ Subgroup.closure (insert z (Set.range w))) :
    x * gprod w l₀ = gprod w l₀ * x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨i, rfl⟩
    · exact h.z_comm _ |>.symm
    · exact h.commute_gprod_univ hodd l₀ hl₀ hall i
  | one => simp
  | mul x y _ _ ihx ihy =>
    calc x * y * gprod w l₀ = x * (y * gprod w l₀) := mul_assoc _ _ _
      _ = x * (gprod w l₀ * y) := by rw [ihy]
      _ = (x * gprod w l₀) * y := (mul_assoc _ _ _).symm
      _ = (gprod w l₀ * x) * y := by rw [ihx]
      _ = gprod w l₀ * (x * y) := mul_assoc _ _ _
  | inv x _ ihx =>
    calc x⁻¹ * gprod w l₀ = x⁻¹ * (gprod w l₀ * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * gprod w l₀) * x⁻¹ := by rw [ihx]
      _ = gprod w l₀ * x⁻¹ := by group

theorem gprod_univ_sq [Fintype Ω] [DecidableEq Ω] (l₀ : List Ω) (hl₀ : l₀.Nodup)
    (hall : ∀ i, i ∈ l₀) :
    gprod w l₀ * gprod w l₀ = z ^ (Nat.choose (Fintype.card Ω) 2) := by
  have hlen : l₀.length = Fintype.card Ω := by
    have : l₀.toFinset = Finset.univ := by
      ext i
      simp [hall i]
    rw [← List.toFinset_card_of_nodup hl₀, this, Finset.card_univ]
  rw [h.gprod_sq hl₀, hlen]

end Prod

end GramRel

end CFSG.Quasithin.SzR1
