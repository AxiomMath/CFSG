module

public import CFSG.LocalAnalysis.StandardType.GGF4WeylQuad
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.StandardType.F4Model

@[expose] def commb (x y : M4) : Bool := x.mul y == y.mul x

theorem commb_iff (x y : M4) : commb x y = true ↔ x.mul y = y.mul x := by
  simp [commb]

theorem Rm_inj : ∀ x, x < 24 → ∀ y, y < 24 → Rm x = Rm y → x = y := by
  decide +kernel

theorem T1_conj_simple :
    ∀ i : Fin 4, ∀ x, x < 24 → ∀ y, y < 24 → (Sm i).mul ((Rm x).mul (Sm i)) = Rm y →
      T1 y = T1 x := by
  decide +kernel

@[expose] def endOk (x0 x1 x2 y : Nat) : Bool :=
  commb (Rm y) (Rm x0) && commb (Rm y) (Rm x1) && commb (Rm y) (Rm x2) && y != x0 && y != x1 &&
    y != x2

@[expose] def chkE2 (x0 x1 : Nat) : Bool :=
  (List.range 24).all fun x2 =>
    if ord2b (Rm x0) (Rm x2) && (ord3b (Rm x1) (Rm x2) || ord4b (Rm x1) (Rm x2)) then
      (List.range 24).any (endOk x0 x1 x2)
    else true

@[expose] def chkE1 (x0 : Nat) : Bool :=
  (List.range 24).all fun x1 => if ord3b (Rm x0) (Rm x1) then chkE2 x0 x1 else true

theorem chkE1_0 : chkE1 0 = true := by decide +kernel

theorem chkE1_1 : chkE1 1 = true := by decide +kernel

theorem chkE1_2 : chkE1 2 = true := by decide +kernel

theorem chkE1_3 : chkE1 3 = true := by decide +kernel

theorem chkE1_4 : chkE1 4 = true := by decide +kernel

theorem chkE1_5 : chkE1 5 = true := by decide +kernel

theorem chkE1_6 : chkE1 6 = true := by decide +kernel

theorem chkE1_7 : chkE1 7 = true := by decide +kernel

theorem chkE1_8 : chkE1 8 = true := by decide +kernel

theorem chkE1_9 : chkE1 9 = true := by decide +kernel

theorem chkE1_10 : chkE1 10 = true := by decide +kernel

theorem chkE1_11 : chkE1 11 = true := by decide +kernel

theorem chkE1_12 : chkE1 12 = true := by decide +kernel

theorem chkE1_13 : chkE1 13 = true := by decide +kernel

theorem chkE1_14 : chkE1 14 = true := by decide +kernel

theorem chkE1_15 : chkE1 15 = true := by decide +kernel

theorem chkE1_16 : chkE1 16 = true := by decide +kernel

theorem chkE1_17 : chkE1 17 = true := by decide +kernel

theorem chkE1_18 : chkE1 18 = true := by decide +kernel

theorem chkE1_19 : chkE1 19 = true := by decide +kernel

theorem chkE1_20 : chkE1 20 = true := by decide +kernel

theorem chkE1_21 : chkE1 21 = true := by decide +kernel

theorem chkE1_22 : chkE1 22 = true := by decide +kernel

theorem chkE1_23 : chkE1 23 = true := by decide +kernel

theorem chkE1_all (x0 : Nat) (hx0 : x0 < 24) : chkE1 x0 = true := by
  interval_cases x0
  exacts [chkE1_0, chkE1_1, chkE1_2, chkE1_3, chkE1_4, chkE1_5, chkE1_6, chkE1_7, chkE1_8,
    chkE1_9, chkE1_10, chkE1_11, chkE1_12, chkE1_13, chkE1_14, chkE1_15, chkE1_16, chkE1_17,
    chkE1_18, chkE1_19, chkE1_20, chkE1_21, chkE1_22, chkE1_23]

theorem endpoint_exists :
    ∀ x0, x0 < 24 → ∀ x1, x1 < 24 → ord3b (Rm x0) (Rm x1) = true →
      ∀ x2, x2 < 24 → ord2b (Rm x0) (Rm x2) = true →
        (ord3b (Rm x1) (Rm x2) = true ∨ ord4b (Rm x1) (Rm x2) = true) →
          ∃ y, y < 24 ∧ endOk x0 x1 x2 y = true := by
  intro x0 hx0 x1 hx1 h01 x2 hx2 h02 h12
  have h1 : chkE2 x0 x1 = true := by
    have h := List.all_eq_true.1 (chkE1_all x0 hx0) x1 (List.mem_range.2 hx1)
    simpa [h01] using h
  have h2 := List.all_eq_true.1 h1 x2 (List.mem_range.2 hx2)
  have h12' : (ord3b (Rm x1) (Rm x2) || ord4b (Rm x1) (Rm x2)) = true := by
    rcases h12 with h | h <;> simp [h]
  simp only [h02, h12', Bool.and_self, if_true] at h2
  obtain ⟨y, hy, hok⟩ := List.any_eq_true.1 h2
  exact ⟨y, List.mem_range.1 hy, hok⟩

@[expose] def chkF1 (a : Nat) : Bool :=
  (List.range 24).all fun b =>
    if T1 b == T1 a && commb (Rm a) (Rm b) then
      (List.range 24).all fun u =>
        if T1 u == T1 a && (u == a || commb (Rm u) (Rm a)) then u == b || commb (Rm u) (Rm b)
        else true
    else true

theorem chkF1_all : ∀ a, a < 24 → chkF1 a = true := by
  decide +kernel

theorem frame_closed :
    ∀ a, a < 24 → ∀ b, b < 24 → T1 b = T1 a → commb (Rm a) (Rm b) = true →
      ∀ u, u < 24 → T1 u = T1 a → (u = a ∨ commb (Rm u) (Rm a) = true) →
        u = b ∨ commb (Rm u) (Rm b) = true := by
  intro a ha b hb hba hab u hu hua hu'
  have h1 := List.all_eq_true.1 (chkF1_all a ha) b (List.mem_range.2 hb)
  simp only [hba, beq_self_eq_true, hab, Bool.and_self, if_true] at h1
  have h2 := List.all_eq_true.1 h1 u (List.mem_range.2 hu)
  have hu'' : (u == a || commb (Rm u) (Rm a)) = true := by
    rcases hu' with rfl | h <;> simp [*]
  simp only [hua, beq_self_eq_true, hu'', Bool.and_self, if_true, Bool.or_eq_true,
    beq_iff_eq] at h2
  exact h2

theorem frame_move :
    ∀ x, x < 24 → ∃ r, r < 24 ∧ commb ((Rm r).mul ((Rm x).mul (Rm r))) (Rm x) = false := by
  decide +kernel

@[expose] def chkP1 (a : Nat) : Bool :=
  (List.range 24).all fun b =>
    if T1 b == T1 a && !commb (Rm a) (Rm b) then
      (List.range 24).all fun c =>
        if T1 c != T1 a then
          (List.range 24).any fun s =>
            commb (Rm s) (Rm a) && commb (Rm s) (Rm b) && !commb (Rm s) (Rm c)
        else true
    else true

theorem chkP1_0 : chkP1 0 = true := by decide +kernel

theorem chkP1_1 : chkP1 1 = true := by decide +kernel

theorem chkP1_2 : chkP1 2 = true := by decide +kernel

theorem chkP1_3 : chkP1 3 = true := by decide +kernel

theorem chkP1_4 : chkP1 4 = true := by decide +kernel

theorem chkP1_5 : chkP1 5 = true := by decide +kernel

theorem chkP1_6 : chkP1 6 = true := by decide +kernel

theorem chkP1_7 : chkP1 7 = true := by decide +kernel

theorem chkP1_8 : chkP1 8 = true := by decide +kernel

theorem chkP1_9 : chkP1 9 = true := by decide +kernel

theorem chkP1_10 : chkP1 10 = true := by decide +kernel

theorem chkP1_11 : chkP1 11 = true := by decide +kernel

theorem chkP1_12 : chkP1 12 = true := by decide +kernel

theorem chkP1_13 : chkP1 13 = true := by decide +kernel

theorem chkP1_14 : chkP1 14 = true := by decide +kernel

theorem chkP1_15 : chkP1 15 = true := by decide +kernel

theorem chkP1_16 : chkP1 16 = true := by decide +kernel

theorem chkP1_17 : chkP1 17 = true := by decide +kernel

theorem chkP1_18 : chkP1 18 = true := by decide +kernel

theorem chkP1_19 : chkP1 19 = true := by decide +kernel

theorem chkP1_20 : chkP1 20 = true := by decide +kernel

theorem chkP1_21 : chkP1 21 = true := by decide +kernel

theorem chkP1_22 : chkP1 22 = true := by decide +kernel

theorem chkP1_23 : chkP1 23 = true := by decide +kernel

theorem chkP1_all (a : Nat) (ha : a < 24) : chkP1 a = true := by
  interval_cases a
  exacts [chkP1_0, chkP1_1, chkP1_2, chkP1_3, chkP1_4, chkP1_5, chkP1_6, chkP1_7, chkP1_8,
    chkP1_9, chkP1_10, chkP1_11, chkP1_12, chkP1_13, chkP1_14, chkP1_15, chkP1_16, chkP1_17,
    chkP1_18, chkP1_19, chkP1_20, chkP1_21, chkP1_22, chkP1_23]

theorem plane_exists :
    ∀ a, a < 24 → ∀ b, b < 24 → T1 b = T1 a → commb (Rm a) (Rm b) = false →
      ∀ c, c < 24 → T1 c ≠ T1 a →
        ∃ s, s < 24 ∧ commb (Rm s) (Rm a) = true ∧ commb (Rm s) (Rm b) = true ∧
          commb (Rm s) (Rm c) = false := by
  intro a ha b hb hba hab c hc hca
  have h1 := List.all_eq_true.1 (chkP1_all a ha) b (List.mem_range.2 hb)
  simp only [hba, beq_self_eq_true, hab, Bool.not_false, Bool.and_self, if_true] at h1
  have h2 := List.all_eq_true.1 h1 c (List.mem_range.2 hc)
  have hca' : (T1 c != T1 a) = true := by simpa using hca
  simp only [hca', if_true] at h2
  obtain ⟨s, hs, hok⟩ := List.any_eq_true.1 h2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  exact ⟨s, List.mem_range.1 hs, hok.1.1, hok.1.2, hok.2⟩

end CFSG.StandardType.F4Model

end
