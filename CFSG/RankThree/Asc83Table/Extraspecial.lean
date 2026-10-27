module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.RankThree.Asc83Table

open Subgroup CFSG.SectionRank.LocalWitness
open scoped commutatorElement

variable {G : Type*} [Group G] {x y : G}

section Identities

variable (hx : x ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
include hx hzx

theorem commutator_pow_three : ⁅x, y⁆ ^ 3 = 1 := by
  rw [commutator_pow_eq hzx, hx, commutatorElement_one_left]

include hzy

theorem y_pow_mul_x_pow (i j : ℕ) : y ^ j * x ^ i = x ^ i * y ^ j * ⁅x, y⁆ ^ (2 * i * j) := by
  have h1 := y_mul_x_pow (r := 3) (by norm_num) hzx hzy (commutator_pow_three hx hzx) i
  induction j with
  | zero => simp
  | succ j ih =>
    have hc : Commute (⁅x, y⁆ ^ (2 * i)) (y ^ j) := (hzy.pow_left _).pow_right _
    calc y ^ (j + 1) * x ^ i = y * (y ^ j * x ^ i) := by rw [pow_succ', mul_assoc]
      _ = y * x ^ i * y ^ j * ⁅x, y⁆ ^ (2 * i * j) := by rw [ih]; simp only [mul_assoc]
      _ = x ^ i * y * (⁅x, y⁆ ^ (2 * i) * y ^ j) * ⁅x, y⁆ ^ (2 * i * j) := by
        rw [h1]; simp only [mul_assoc]
      _ = x ^ i * y * (y ^ j * ⁅x, y⁆ ^ (2 * i)) * ⁅x, y⁆ ^ (2 * i * j) := by rw [hc.eq]
      _ = x ^ i * y ^ (j + 1) * ⁅x, y⁆ ^ (2 * i * (j + 1)) := by
        rw [pow_succ' y j, show 2 * i * (j + 1) = 2 * i + 2 * i * j by ring, pow_add]
        simp only [mul_assoc]

theorem sq_x_pow_mul_y_pow (i j : ℕ) :
    (x ^ i * y ^ j) ^ 2 = x ^ (2 * i) * y ^ (2 * j) * ⁅x, y⁆ ^ (2 * i * j) := by
  have hc : Commute (⁅x, y⁆ ^ (2 * i * j)) (y ^ j) := (hzy.pow_left _).pow_right _
  calc (x ^ i * y ^ j) ^ 2 = x ^ i * (y ^ j * x ^ i) * y ^ j := by
        rw [sq]; simp only [mul_assoc]
    _ = x ^ i * x ^ i * y ^ j * (⁅x, y⁆ ^ (2 * i * j) * y ^ j) := by
        rw [y_pow_mul_x_pow hx hzx hzy]; simp only [mul_assoc]
    _ = x ^ (2 * i) * y ^ (2 * j) * ⁅x, y⁆ ^ (2 * i * j) := by
        rw [hc.eq, two_mul, two_mul, pow_add, pow_add]; simp only [mul_assoc]

theorem cube_x_pow_mul_y_pow (i j : ℕ) :
    (x ^ i * y ^ j) ^ 3 = x ^ (3 * i) * y ^ (3 * j) * ⁅x, y⁆ ^ (6 * i * j) := by
  have hc1 : Commute (⁅x, y⁆ ^ (2 * i * j)) (x ^ i * y ^ j) :=
    (hzx.pow_left _).pow_right _ |>.mul_right ((hzy.pow_left _).pow_right _)
  have hc2 : Commute (⁅x, y⁆ ^ (2 * i * (2 * j))) (y ^ j) := (hzy.pow_left _).pow_right _
  calc (x ^ i * y ^ j) ^ 3 = (x ^ i * y ^ j) ^ 2 * (x ^ i * y ^ j) := by rw [pow_succ]
    _ = x ^ (2 * i) * y ^ (2 * j) * (⁅x, y⁆ ^ (2 * i * j) * (x ^ i * y ^ j)) := by
        rw [sq_x_pow_mul_y_pow hx hzx hzy]; simp only [mul_assoc]
    _ = x ^ (2 * i) * (y ^ (2 * j) * x ^ i) * y ^ j * ⁅x, y⁆ ^ (2 * i * j) := by
        rw [hc1.eq]; simp only [mul_assoc]
    _ = x ^ (2 * i) * x ^ i * y ^ (2 * j) * (⁅x, y⁆ ^ (2 * i * (2 * j)) * y ^ j) *
          ⁅x, y⁆ ^ (2 * i * j) := by
        rw [y_pow_mul_x_pow hx hzx hzy]; simp only [mul_assoc]
    _ = x ^ (3 * i) * y ^ (3 * j) * ⁅x, y⁆ ^ (6 * i * j) := by
        rw [hc2.eq, show 3 * i = 2 * i + i by ring, show 3 * j = 2 * j + j by ring,
          show 6 * i * j = 2 * i * (2 * j) + 2 * i * j by ring, pow_add, pow_add, pow_add]
        simp only [mul_assoc]

variable (hy : y ^ 3 = 1)
include hy

theorem sq_x_sq_mul_y_sq : (x ^ 2 * y ^ 2) ^ 2 * ⁅x, y⁆ = x * y := by
  have hz := commutator_pow_three hx hzx
  have hx4 : x ^ 4 = x := by rw [pow_succ, hx, one_mul]
  have hy4 : y ^ 4 = y := by rw [pow_succ, hy, one_mul]
  have hz8 : ⁅x, y⁆ ^ 8 = ⁅x, y⁆ ^ 2 := by
    rw [show 8 = 3 * 2 + 2 by rfl, pow_add, pow_mul, hz, one_pow, one_mul]
  rw [sq_x_pow_mul_y_pow hx hzx hzy 2 2, show 2 * 2 = 4 by rfl, show 2 * 2 * 2 = 8 by rfl, hx4,
    hy4, hz8, mul_assoc, ← pow_succ, hz, mul_one]

omit hy in
theorem sq_x_sq_mul_y_mul_sq : (x ^ 2 * y ^ 1) ^ 2 * ⁅x, y⁆ ^ 2 = x * y ^ 2 := by
  have hz := commutator_pow_three hx hzx
  have hx4 : x ^ 4 = x := by rw [pow_succ, hx, one_mul]
  have hz4 : ⁅x, y⁆ ^ 4 = ⁅x, y⁆ := by rw [pow_succ, hz, one_mul]
  rw [sq_x_pow_mul_y_pow hx hzx hzy 2 1]
  simp only [show 2 * 2 = 4 from rfl, show 2 * 1 = 2 from rfl]
  rw [hx4, hz4, mul_assoc, ← pow_succ', hz, mul_one]

theorem cube_x_pow_mul_y_pow_eq_one (i j : ℕ) : (x ^ i * y ^ j) ^ 3 = 1 := by
  have hz := commutator_pow_three hx hzx
  rw [cube_x_pow_mul_y_pow hx hzx hzy, pow_mul, pow_mul, show 6 * i * j = 3 * (2 * i * j) by ring,
    pow_mul, hx, hy, hz, one_pow, one_pow, one_pow, one_mul, one_mul]

theorem pow_three_eq_one_of_mem {g : G} (hg : g ∈ Subgroup.closure ({x, y} : Set G)) :
    g ^ 3 = 1 := by
  obtain ⟨i, j, k, -, -, -, rfl⟩ := mem_closure_normalForm (by norm_num) hx hy hzx hzy hg
  have hc : Commute (⁅x, y⁆ ^ k) (x ^ i * y ^ j) :=
    (hzx.pow_left _).pow_right _ |>.mul_right ((hzy.pow_left _).pow_right _)
  rw [hc.symm.mul_pow, cube_x_pow_mul_y_pow_eq_one hx hzx hzy hy, ← pow_mul, mul_comm, pow_mul,
    commutator_pow_three hx hzx, one_pow, one_mul]

end Identities

section Subgroups

variable (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
  (hcard : Nat.card (closure ({x, y} : Set G)) = 27)
include hx hy hzx hzy hcard

theorem normalForm_injective :
    Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 =>
      x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ) := by
  set P := closure ({x, y} : Set G)
  have hxP : x ∈ P := subset_closure (by simp)
  have hyP : y ∈ P := subset_closure (by simp)
  have hzP : ⁅x, y⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hxP hyP) (P.inv_mem hxP)) (P.inv_mem hyP)
  let F : Fin 3 × Fin 3 × Fin 3 → P := fun t =>
    ⟨x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ),
      P.mul_mem (P.mul_mem (P.pow_mem hxP _) (P.pow_mem hyP _)) (P.pow_mem hzP _)⟩
  have hF : Function.Surjective F := fun g => by
    obtain ⟨i, j, k, hi, hj, hk, hg⟩ := mem_closure_normalForm (by norm_num) hx hy hzx hzy g.2
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), Subtype.ext hg.symm⟩
  have hinj : Function.Injective F :=
    (hF.bijective_of_nat_card_le (by rw [hcard]; simp)).1
  intro a b hab
  exact hinj (Subtype.ext hab)

theorem commutator_ne_one_of_card : ⁅x, y⁆ ≠ 1 := by
  intro h1
  have h := @normalForm_injective G _ x y hx hy hzx hzy hcard (0, 0, 0) (0, 0, 1)
    (by simp only [h1, one_pow])
  exact absurd (congrArg (fun t : Fin 3 × Fin 3 × Fin 3 => t.2.2) h) (by decide)

theorem eq_zero_of_mem_zpowers {i j : ℕ} (hi : i < 3) (hj : j < 3)
    (h : x ^ i * y ^ j ∈ zpowers ⁅x, y⁆) : i = 0 ∧ j = 0 := by
  have hz := commutator_pow_three hx hzx
  have hord : orderOf ⁅x, y⁆ = 3 :=
    orderOf_eq_prime hz (commutator_ne_one_of_card hx hy hzx hzy hcard)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
  rw [← zpow_mod_orderOf, hord] at hk
  have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  set m := (k % ((3 : ℕ) : ℤ)).toNat with hmdef
  have hm : m < 3 := by omega
  have hme : ⁅x, y⁆ ^ m = x ^ i * y ^ j := by
    rw [← hk, ← zpow_natCast, hmdef, Int.toNat_of_nonneg h0]
  have h := @normalForm_injective G _ x y hx hy hzx hzy hcard (⟨i, hi⟩, ⟨j, hj⟩, 0) (0, 0, ⟨m, hm⟩)
    (by simp only [Fin.val_zero, pow_zero, mul_one, one_mul]; exact hme.symm)
  exact ⟨congrArg (fun t : Fin 3 × Fin 3 × Fin 3 => (t.1 : ℕ)) h,
    congrArg (fun t : Fin 3 × Fin 3 × Fin 3 => (t.2.1 : ℕ)) h⟩

omit hx hy hzx hzy in
theorem commutator_mem_of_card_eq_nine {B : Subgroup G} (hB : B ≤ closure {x, y})
    (hB9 : Nat.card B = 9) : ⁅x, y⁆ ∈ B := by
  set P := closure ({x, y} : Set G)
  set B' := B.subgroupOf P
  have hB'card : Nat.card B' = 9 := by
    rw [← hB9]
    exact Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv
  have hidx : B'.index = 3 := by
    have h := B'.index_mul_card
    rw [hB'card, hcard] at h
    omega
  have hmin : (Nat.card P).minFac = 3 := by rw [hcard]; norm_num
  have : B'.Normal := normal_of_index_eq_minFac_card (by rw [hidx, hmin])
  have hq : Nat.card (P ⧸ B') = 3 := hidx
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : IsCyclic (P ⧸ B') := isCyclic_of_prime_card hq
  let _ : CommGroup (P ⧸ B') := IsCyclic.commGroup
  have hxP : x ∈ P := subset_closure (by simp)
  have hyP : y ∈ P := subset_closure (by simp)
  have hc : QuotientGroup.mk' B' ⁅(⟨x, hxP⟩ : P), ⟨y, hyP⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hc
  exact hc

theorem eq_closure_of_mem {B : Subgroup G} (hB : B ≤ closure {x, y}) (hB9 : Nat.card B = 9)
    {u : G} (hu : u ∈ B) (hu' : u ∉ zpowers ⁅x, y⁆) : B = closure {⁅x, y⁆, u} := by
  have hzB := commutator_mem_of_card_eq_nine hcard hB hB9
  have hle : closure {⁅x, y⁆, u} ≤ B := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hzB
    · exact hu
  have hzle : zpowers ⁅x, y⁆ ≤ closure {⁅x, y⁆, u} := by
    rw [zpowers_le]
    exact subset_closure (by simp)
  have : Finite B := Nat.finite_of_card_ne_zero (by rw [hB9]; norm_num)
  have hz3 : Nat.card (zpowers ⁅x, y⁆) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (commutator_pow_three hx hzx)
      (commutator_ne_one_of_card hx hy hzx hzy hcard)
  have hd9 : Nat.card (closure {⁅x, y⁆, u}) ∣ 9 := hB9 ▸ card_dvd_of_le hle
  have hd3 : 3 ∣ Nat.card (closure {⁅x, y⁆, u}) := hz3 ▸ card_dvd_of_le hzle
  have hne3 : Nat.card (closure {⁅x, y⁆, u}) ≠ 3 := by
    intro h3
    have : Finite (closure {⁅x, y⁆, u}) := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
    have heq : zpowers ⁅x, y⁆ = closure {⁅x, y⁆, u} :=
      Subgroup.eq_of_le_of_card_ge hzle (by rw [h3, hz3])
    exact hu' (heq ▸ subset_closure (by simp))
  have h9 : Nat.card (closure {⁅x, y⁆, u}) = 9 := by
    have : Nat.card (closure {⁅x, y⁆, u}) ∈ Nat.divisors 9 :=
      Nat.mem_divisors.2 ⟨hd9, by norm_num⟩
    have hdiv : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · rw [h] at hd3; norm_num at hd3
    · exact absurd h hne3
    · exact h
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hB9])).symm

theorem eq_of_le_of_card_eq_nine {B : Subgroup G} (hB : B ≤ closure {x, y})
    (hB9 : Nat.card B = 9) :
    B = closure {⁅x, y⁆, x} ∨ B = closure {⁅x, y⁆, y} ∨ B = closure {⁅x, y⁆, x * y} ∨
      B = closure {⁅x, y⁆, x * y ^ 2} := by
  have hzB := commutator_mem_of_card_eq_nine hcard hB hB9
  have hz := commutator_pow_three hx hzx
  obtain ⟨w, hwB, hw⟩ : ∃ w ∈ B, w ∉ zpowers ⁅x, y⁆ := by
    by_contra hcon
    push Not at hcon
    have hle : B ≤ zpowers ⁅x, y⁆ := hcon
    have := card_dvd_of_le hle
    rw [hB9, Nat.card_zpowers, orderOf_eq_prime hz
      (commutator_ne_one_of_card hx hy hzx hzy hcard)] at this
    norm_num at this
  obtain ⟨i, j, k, hi, hj, hk, rfl⟩ :=
    mem_closure_normalForm (by norm_num) hx hy hzx hzy (hB hwB)
  have huB : x ^ i * y ^ j ∈ B := by
    have := B.mul_mem hwB (B.pow_mem (B.inv_mem hzB) k)
    rwa [inv_pow, mul_inv_cancel_right] at this
  have hij : ¬ (i = 0 ∧ j = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hw (by simp [pow_mem (mem_zpowers ⁅x, y⁆) k])
  have hout : ∀ {a b : ℕ}, a < 3 → b < 3 → ¬ (a = 0 ∧ b = 0) →
      x ^ a * y ^ b ∉ zpowers ⁅x, y⁆ := fun ha hb hab hmem =>
    hab (eq_zero_of_mem_zpowers hx hy hzx hzy hcard ha hb hmem)
  have key : ∀ {a b : ℕ}, a < 3 → b < 3 → ¬ (a = 0 ∧ b = 0) → x ^ a * y ^ b ∈ B →
      B = closure {⁅x, y⁆, x ^ a * y ^ b} := fun ha hb hab hm =>
    eq_closure_of_mem hx hy hzx hzy hcard hB hB9 hm (hout ha hb hab)
  interval_cases i <;> interval_cases j
  · exact absurd ⟨rfl, rfl⟩ hij
  ·
    right; left; simpa using key (a := 0) (b := 1) (by norm_num) (by norm_num) (by simp) huB
  ·
    right; left
    have hyB : y ∈ B := by
      have h2 : (x ^ 0 * y ^ 2) ^ 2 = y := by
        rw [pow_zero, one_mul, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hy, one_mul, pow_one]
      exact h2 ▸ B.pow_mem huB 2
    simpa using key (a := 0) (b := 1) (by norm_num) (by norm_num) (by simp) (by simpa using hyB)
  ·
    left; simpa using key (a := 1) (b := 0) (by norm_num) (by norm_num) (by simp) huB
  ·
    right; right; left; simpa using key (a := 1) (b := 1) (by norm_num) (by norm_num) (by simp) huB
  ·
    right; right; right; simpa using key (a := 1) (b := 2) (by norm_num) (by norm_num) (by simp) huB
  ·
    left
    have hxB : x ∈ B := by
      have h2 : (x ^ 2 * y ^ 0) ^ 2 = x := by
        rw [pow_zero, mul_one, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hx, one_mul, pow_one]
      exact h2 ▸ B.pow_mem huB 2
    simpa using key (a := 1) (b := 0) (by norm_num) (by norm_num) (by simp) (by simpa using hxB)
  ·
    right; right; right
    have hB' : x * y ^ 2 ∈ B := by
      rw [← sq_x_sq_mul_y_mul_sq hx hzx hzy]
      exact B.mul_mem (B.pow_mem huB 2) (B.pow_mem hzB 2)
    simpa using key (a := 1) (b := 2) (by norm_num) (by norm_num) (by simp) (by simpa using hB')
  ·
    right; right; left
    have hB' : x * y ∈ B := by
      rw [← sq_x_sq_mul_y_sq hx hzx hzy hy]
      exact B.mul_mem (B.pow_mem huB 2) hzB
    simpa using key (a := 1) (b := 1) (by norm_num) (by norm_num) (by simp) (by simpa using hB')

end Subgroups

end CFSG.RankThree.Asc83Table
