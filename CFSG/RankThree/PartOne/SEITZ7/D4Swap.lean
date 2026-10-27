module

public import CFSG.LieType.Steinberg.TwistedD4.Unipotent
public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.Timmesfeld.RankTwo.ModelG2Comm

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open scoped commutatorElement

variable {K : Type} [Field K]

noncomputable abbrev xd (p : ℕ) (c : K) : adjointGroup d4 K :=
  xPar (rootOperatorFamily d4) (d4Root p) c

theorem xd_add (p : ℕ) (c d : K) : xd p (c + d) = xd p c * xd p d := xPar_add _ _ _

theorem xd_zero (p : ℕ) : xd p (0 : K) = 1 := by
  have := xd_add (K := K) p 0 0
  simpa using this

theorem xd_mul_self [CharP K 2] (p : ℕ) (c : K) : xd p c * xd p c = 1 := by
  rw [← xd_add, CharTwo.add_self_eq_zero, xd_zero]

theorem xd_inv [CharP K 2] (p : ℕ) (c : K) : (xd p c)⁻¹ = xd p c :=
  inv_eq_of_mul_eq_one_right (xd_mul_self p c)

theorem swap_of_comm' {G : Type*} [Group G] (g h z : G) (hz : ⁅g, h⁆ = z) :
    g * h = z * (h * g) := by
  rw [← hz, commutatorElement_def]
  group

theorem cast_sign_eq [CharP K 2] {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : ((ε : ℤ) : K) = 1 := by
  rcases hε with rfl | rfl <;> simp [CharTwo.neg_eq]

theorem swap_gen [CharP K 2] {b a c : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : RootOps.repCheck d4 b a [(1, 1, c, ε)] = true) (x y : K) :
    xd b y * xd a x = xd c (x * y) * (xd a x * xd b y) := by
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := d4) (K := K) h y x
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
    cast_sign_eq hε, one_mul] at this
  refine swap_of_comm' _ _ _ ?_
  rw [this, mul_comm y x]

theorem commute_gen [CharP K 2] {b a : ℕ} (h : RootOps.repCheck d4 b a [] = true) (x y : K) :
    Commute (xd b x) (xd a y) := by
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := d4) (K := K) h x y
  simp only [List.map_nil, List.prod_nil] at this
  exact commutatorElement_eq_one_iff_commute.1 this

theorem swap_0_2 [CharP K 2] (x y : K) :
    xd 0 y * xd 2 x = xd 5 (x * y) * (xd 2 x * xd 0 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_1_2 [CharP K 2] (x y : K) :
    xd 1 y * xd 2 x = xd 7 (x * y) * (xd 2 x * xd 1 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_3_2 [CharP K 2] (x y : K) :
    xd 3 y * xd 2 x = xd 9 (x * y) * (xd 2 x * xd 3 y) :=
  swap_gen (Or.inl rfl) (by decide +kernel) x y

theorem swap_5_1 [CharP K 2] (x y : K) :
    xd 5 y * xd 1 x = xd 12 (x * y) * (xd 1 x * xd 5 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_5_3 [CharP K 2] (x y : K) :
    xd 5 y * xd 3 x = xd 13 (x * y) * (xd 3 x * xd 5 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_7_0 [CharP K 2] (x y : K) :
    xd 7 y * xd 0 x = xd 12 (x * y) * (xd 0 x * xd 7 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_7_3 [CharP K 2] (x y : K) :
    xd 7 y * xd 3 x = xd 15 (x * y) * (xd 3 x * xd 7 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_9_0 [CharP K 2] (x y : K) :
    xd 9 y * xd 0 x = xd 13 (x * y) * (xd 0 x * xd 9 y) :=
  swap_gen (Or.inl rfl) (by decide +kernel) x y

theorem swap_9_1 [CharP K 2] (x y : K) :
    xd 9 y * xd 1 x = xd 15 (x * y) * (xd 1 x * xd 9 y) :=
  swap_gen (Or.inl rfl) (by decide +kernel) x y

theorem swap_12_3 [CharP K 2] (x y : K) :
    xd 12 y * xd 3 x = xd 19 (x * y) * (xd 3 x * xd 12 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_12_9 [CharP K 2] (x y : K) :
    xd 12 y * xd 9 x = xd 22 (x * y) * (xd 9 x * xd 12 y) :=
  swap_gen (Or.inl rfl) (by decide +kernel) x y

theorem swap_13_1 [CharP K 2] (x y : K) :
    xd 13 y * xd 1 x = xd 19 (x * y) * (xd 1 x * xd 13 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_13_7 [CharP K 2] (x y : K) :
    xd 13 y * xd 7 x = xd 22 (x * y) * (xd 7 x * xd 13 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_15_0 [CharP K 2] (x y : K) :
    xd 15 y * xd 0 x = xd 19 (x * y) * (xd 0 x * xd 15 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_15_5 [CharP K 2] (x y : K) :
    xd 15 y * xd 5 x = xd 22 (x * y) * (xd 5 x * xd 15 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem swap_19_2 [CharP K 2] (x y : K) :
    xd 19 y * xd 2 x = xd 22 (x * y) * (xd 2 x * xd 19 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem commute_1_0 [CharP K 2] (x y : K) : Commute (xd 1 x) (xd 0 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_3_0 [CharP K 2] (x y : K) : Commute (xd 3 x) (xd 0 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_3_1 [CharP K 2] (x y : K) : Commute (xd 3 x) (xd 1 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_5_2 [CharP K 2] (x y : K) : Commute (xd 5 x) (xd 2 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_5_0 [CharP K 2] (x y : K) : Commute (xd 5 x) (xd 0 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_7_2 [CharP K 2] (x y : K) : Commute (xd 7 x) (xd 2 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_7_1 [CharP K 2] (x y : K) : Commute (xd 7 x) (xd 1 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_7_5 [CharP K 2] (x y : K) : Commute (xd 7 x) (xd 5 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_9_2 [CharP K 2] (x y : K) : Commute (xd 9 x) (xd 2 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_9_3 [CharP K 2] (x y : K) : Commute (xd 9 x) (xd 3 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_9_5 [CharP K 2] (x y : K) : Commute (xd 9 x) (xd 5 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_9_7 [CharP K 2] (x y : K) : Commute (xd 9 x) (xd 7 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_12_2 [CharP K 2] (x y : K) : Commute (xd 12 x) (xd 2 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_12_0 [CharP K 2] (x y : K) : Commute (xd 12 x) (xd 0 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_12_1 [CharP K 2] (x y : K) : Commute (xd 12 x) (xd 1 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_12_5 [CharP K 2] (x y : K) : Commute (xd 12 x) (xd 5 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_12_7 [CharP K 2] (x y : K) : Commute (xd 12 x) (xd 7 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_13_2 [CharP K 2] (x y : K) : Commute (xd 13 x) (xd 2 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_13_0 [CharP K 2] (x y : K) : Commute (xd 13 x) (xd 0 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_13_3 [CharP K 2] (x y : K) : Commute (xd 13 x) (xd 3 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_13_5 [CharP K 2] (x y : K) : Commute (xd 13 x) (xd 5 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_13_9 [CharP K 2] (x y : K) : Commute (xd 13 x) (xd 9 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_13_12 [CharP K 2] (x y : K) : Commute (xd 13 x) (xd 12 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_15_2 [CharP K 2] (x y : K) : Commute (xd 15 x) (xd 2 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_15_1 [CharP K 2] (x y : K) : Commute (xd 15 x) (xd 1 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_15_3 [CharP K 2] (x y : K) : Commute (xd 15 x) (xd 3 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_15_7 [CharP K 2] (x y : K) : Commute (xd 15 x) (xd 7 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_15_9 [CharP K 2] (x y : K) : Commute (xd 15 x) (xd 9 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_15_12 [CharP K 2] (x y : K) : Commute (xd 15 x) (xd 12 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_15_13 [CharP K 2] (x y : K) : Commute (xd 15 x) (xd 13 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_19_0 [CharP K 2] (x y : K) : Commute (xd 19 x) (xd 0 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_19_1 [CharP K 2] (x y : K) : Commute (xd 19 x) (xd 1 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_19_3 [CharP K 2] (x y : K) : Commute (xd 19 x) (xd 3 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_19_5 [CharP K 2] (x y : K) : Commute (xd 19 x) (xd 5 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_19_7 [CharP K 2] (x y : K) : Commute (xd 19 x) (xd 7 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_19_9 [CharP K 2] (x y : K) : Commute (xd 19 x) (xd 9 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_19_12 [CharP K 2] (x y : K) : Commute (xd 19 x) (xd 12 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_19_13 [CharP K 2] (x y : K) : Commute (xd 19 x) (xd 13 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_19_15 [CharP K 2] (x y : K) : Commute (xd 19 x) (xd 15 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_2 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 2 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_0 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 0 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_1 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 1 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_3 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 3 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_5 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 5 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_7 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 7 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_9 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 9 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_12 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 12 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_13 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 13 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_15 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 15 y) :=
  commute_gen (by decide +kernel) x y

theorem commute_22_19 [CharP K 2] (x y : K) : Commute (xd 22 x) (xd 19 y) :=
  commute_gen (by decide +kernel) x y

section Collection

theorem xd_merge (p : ℕ) (c d : K) (z : adjointGroup d4 K) :
    xd p c * (xd p d * z) = xd p (c + d) * z := by
  rw [← mul_assoc, ← xd_add]

theorem xd_merge' (p : ℕ) (c d : K) : xd p c * xd p d = xd p (c + d) := (xd_add p c d).symm

theorem comm_tail {p q : ℕ} {x y : K} (h : Commute (xd p x) (xd q y))
    (z : adjointGroup d4 K) : xd p x * (xd q y * z) = xd q y * (xd p x * z) := by
  rw [← mul_assoc, h.eq, mul_assoc]

theorem swap_tail {p q r : ℕ} {x y : K} {c : K} (h : xd p x * xd q y = xd r c * (xd q y * xd p x))
    (z : adjointGroup d4 K) :
    xd p x * (xd q y * z) = xd r c * (xd q y * (xd p x * z)) := by
  rw [← mul_assoc, h]
  simp only [mul_assoc]

variable [CharP K 2]

theorem xd_cancel (p : ℕ) (c : K) (z : adjointGroup d4 K) : xd p c * (xd p c * z) = z := by
  rw [xd_merge, CharTwo.add_self_eq_zero, xd_zero, one_mul]

theorem xd_cancel' (p : ℕ) (c : K) : xd p c * xd p c = 1 := xd_mul_self p c

theorem tail_1_0 (x y : K) (z : adjointGroup d4 K) :
    xd 1 x * (xd 0 y * z) = xd 0 y * (xd 1 x * z) :=
  comm_tail (commute_1_0 x y) z
theorem end_1_0 (x y : K) : xd 1 x * xd 0 y = xd 0 y * xd 1 x :=
  (commute_1_0 x y).eq
theorem tail_3_0 (x y : K) (z : adjointGroup d4 K) :
    xd 3 x * (xd 0 y * z) = xd 0 y * (xd 3 x * z) :=
  comm_tail (commute_3_0 x y) z
theorem end_3_0 (x y : K) : xd 3 x * xd 0 y = xd 0 y * xd 3 x :=
  (commute_3_0 x y).eq
theorem tail_3_1 (x y : K) (z : adjointGroup d4 K) :
    xd 3 x * (xd 1 y * z) = xd 1 y * (xd 3 x * z) :=
  comm_tail (commute_3_1 x y) z
theorem end_3_1 (x y : K) : xd 3 x * xd 1 y = xd 1 y * xd 3 x :=
  (commute_3_1 x y).eq
theorem tail_5_2 (x y : K) (z : adjointGroup d4 K) :
    xd 5 x * (xd 2 y * z) = xd 2 y * (xd 5 x * z) :=
  comm_tail (commute_5_2 x y) z
theorem end_5_2 (x y : K) : xd 5 x * xd 2 y = xd 2 y * xd 5 x :=
  (commute_5_2 x y).eq
theorem tail_5_0 (x y : K) (z : adjointGroup d4 K) :
    xd 5 x * (xd 0 y * z) = xd 0 y * (xd 5 x * z) :=
  comm_tail (commute_5_0 x y) z
theorem end_5_0 (x y : K) : xd 5 x * xd 0 y = xd 0 y * xd 5 x :=
  (commute_5_0 x y).eq
theorem tail_7_2 (x y : K) (z : adjointGroup d4 K) :
    xd 7 x * (xd 2 y * z) = xd 2 y * (xd 7 x * z) :=
  comm_tail (commute_7_2 x y) z
theorem end_7_2 (x y : K) : xd 7 x * xd 2 y = xd 2 y * xd 7 x :=
  (commute_7_2 x y).eq
theorem tail_7_1 (x y : K) (z : adjointGroup d4 K) :
    xd 7 x * (xd 1 y * z) = xd 1 y * (xd 7 x * z) :=
  comm_tail (commute_7_1 x y) z
theorem end_7_1 (x y : K) : xd 7 x * xd 1 y = xd 1 y * xd 7 x :=
  (commute_7_1 x y).eq
theorem tail_7_5 (x y : K) (z : adjointGroup d4 K) :
    xd 7 x * (xd 5 y * z) = xd 5 y * (xd 7 x * z) :=
  comm_tail (commute_7_5 x y) z
theorem end_7_5 (x y : K) : xd 7 x * xd 5 y = xd 5 y * xd 7 x :=
  (commute_7_5 x y).eq
theorem tail_9_2 (x y : K) (z : adjointGroup d4 K) :
    xd 9 x * (xd 2 y * z) = xd 2 y * (xd 9 x * z) :=
  comm_tail (commute_9_2 x y) z
theorem end_9_2 (x y : K) : xd 9 x * xd 2 y = xd 2 y * xd 9 x :=
  (commute_9_2 x y).eq
theorem tail_9_3 (x y : K) (z : adjointGroup d4 K) :
    xd 9 x * (xd 3 y * z) = xd 3 y * (xd 9 x * z) :=
  comm_tail (commute_9_3 x y) z
theorem end_9_3 (x y : K) : xd 9 x * xd 3 y = xd 3 y * xd 9 x :=
  (commute_9_3 x y).eq
theorem tail_9_5 (x y : K) (z : adjointGroup d4 K) :
    xd 9 x * (xd 5 y * z) = xd 5 y * (xd 9 x * z) :=
  comm_tail (commute_9_5 x y) z
theorem end_9_5 (x y : K) : xd 9 x * xd 5 y = xd 5 y * xd 9 x :=
  (commute_9_5 x y).eq
theorem tail_9_7 (x y : K) (z : adjointGroup d4 K) :
    xd 9 x * (xd 7 y * z) = xd 7 y * (xd 9 x * z) :=
  comm_tail (commute_9_7 x y) z
theorem end_9_7 (x y : K) : xd 9 x * xd 7 y = xd 7 y * xd 9 x :=
  (commute_9_7 x y).eq
theorem tail_12_2 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 2 y * z) = xd 2 y * (xd 12 x * z) :=
  comm_tail (commute_12_2 x y) z
theorem end_12_2 (x y : K) : xd 12 x * xd 2 y = xd 2 y * xd 12 x :=
  (commute_12_2 x y).eq
theorem tail_12_0 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 0 y * z) = xd 0 y * (xd 12 x * z) :=
  comm_tail (commute_12_0 x y) z
theorem end_12_0 (x y : K) : xd 12 x * xd 0 y = xd 0 y * xd 12 x :=
  (commute_12_0 x y).eq
theorem tail_12_1 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 1 y * z) = xd 1 y * (xd 12 x * z) :=
  comm_tail (commute_12_1 x y) z
theorem end_12_1 (x y : K) : xd 12 x * xd 1 y = xd 1 y * xd 12 x :=
  (commute_12_1 x y).eq
theorem tail_12_5 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 5 y * z) = xd 5 y * (xd 12 x * z) :=
  comm_tail (commute_12_5 x y) z
theorem end_12_5 (x y : K) : xd 12 x * xd 5 y = xd 5 y * xd 12 x :=
  (commute_12_5 x y).eq
theorem tail_12_7 (x y : K) (z : adjointGroup d4 K) :
    xd 12 x * (xd 7 y * z) = xd 7 y * (xd 12 x * z) :=
  comm_tail (commute_12_7 x y) z
theorem end_12_7 (x y : K) : xd 12 x * xd 7 y = xd 7 y * xd 12 x :=
  (commute_12_7 x y).eq
theorem tail_13_2 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 2 y * z) = xd 2 y * (xd 13 x * z) :=
  comm_tail (commute_13_2 x y) z
theorem end_13_2 (x y : K) : xd 13 x * xd 2 y = xd 2 y * xd 13 x :=
  (commute_13_2 x y).eq
theorem tail_13_0 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 0 y * z) = xd 0 y * (xd 13 x * z) :=
  comm_tail (commute_13_0 x y) z
theorem end_13_0 (x y : K) : xd 13 x * xd 0 y = xd 0 y * xd 13 x :=
  (commute_13_0 x y).eq
theorem tail_13_3 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 3 y * z) = xd 3 y * (xd 13 x * z) :=
  comm_tail (commute_13_3 x y) z
theorem end_13_3 (x y : K) : xd 13 x * xd 3 y = xd 3 y * xd 13 x :=
  (commute_13_3 x y).eq
theorem tail_13_5 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 5 y * z) = xd 5 y * (xd 13 x * z) :=
  comm_tail (commute_13_5 x y) z
theorem end_13_5 (x y : K) : xd 13 x * xd 5 y = xd 5 y * xd 13 x :=
  (commute_13_5 x y).eq
theorem tail_13_9 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 9 y * z) = xd 9 y * (xd 13 x * z) :=
  comm_tail (commute_13_9 x y) z
theorem end_13_9 (x y : K) : xd 13 x * xd 9 y = xd 9 y * xd 13 x :=
  (commute_13_9 x y).eq
theorem tail_13_12 (x y : K) (z : adjointGroup d4 K) :
    xd 13 x * (xd 12 y * z) = xd 12 y * (xd 13 x * z) :=
  comm_tail (commute_13_12 x y) z
theorem end_13_12 (x y : K) : xd 13 x * xd 12 y = xd 12 y * xd 13 x :=
  (commute_13_12 x y).eq
theorem tail_15_2 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 2 y * z) = xd 2 y * (xd 15 x * z) :=
  comm_tail (commute_15_2 x y) z
theorem end_15_2 (x y : K) : xd 15 x * xd 2 y = xd 2 y * xd 15 x :=
  (commute_15_2 x y).eq
theorem tail_15_1 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 1 y * z) = xd 1 y * (xd 15 x * z) :=
  comm_tail (commute_15_1 x y) z
theorem end_15_1 (x y : K) : xd 15 x * xd 1 y = xd 1 y * xd 15 x :=
  (commute_15_1 x y).eq
theorem tail_15_3 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 3 y * z) = xd 3 y * (xd 15 x * z) :=
  comm_tail (commute_15_3 x y) z
theorem end_15_3 (x y : K) : xd 15 x * xd 3 y = xd 3 y * xd 15 x :=
  (commute_15_3 x y).eq
theorem tail_15_7 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 7 y * z) = xd 7 y * (xd 15 x * z) :=
  comm_tail (commute_15_7 x y) z
theorem end_15_7 (x y : K) : xd 15 x * xd 7 y = xd 7 y * xd 15 x :=
  (commute_15_7 x y).eq
theorem tail_15_9 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 9 y * z) = xd 9 y * (xd 15 x * z) :=
  comm_tail (commute_15_9 x y) z
theorem end_15_9 (x y : K) : xd 15 x * xd 9 y = xd 9 y * xd 15 x :=
  (commute_15_9 x y).eq
theorem tail_15_12 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 12 y * z) = xd 12 y * (xd 15 x * z) :=
  comm_tail (commute_15_12 x y) z
theorem end_15_12 (x y : K) : xd 15 x * xd 12 y = xd 12 y * xd 15 x :=
  (commute_15_12 x y).eq
theorem tail_15_13 (x y : K) (z : adjointGroup d4 K) :
    xd 15 x * (xd 13 y * z) = xd 13 y * (xd 15 x * z) :=
  comm_tail (commute_15_13 x y) z
theorem end_15_13 (x y : K) : xd 15 x * xd 13 y = xd 13 y * xd 15 x :=
  (commute_15_13 x y).eq
theorem tail_19_0 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 0 y * z) = xd 0 y * (xd 19 x * z) :=
  comm_tail (commute_19_0 x y) z
theorem end_19_0 (x y : K) : xd 19 x * xd 0 y = xd 0 y * xd 19 x :=
  (commute_19_0 x y).eq
theorem tail_19_1 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 1 y * z) = xd 1 y * (xd 19 x * z) :=
  comm_tail (commute_19_1 x y) z
theorem end_19_1 (x y : K) : xd 19 x * xd 1 y = xd 1 y * xd 19 x :=
  (commute_19_1 x y).eq
theorem tail_19_3 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 3 y * z) = xd 3 y * (xd 19 x * z) :=
  comm_tail (commute_19_3 x y) z
theorem end_19_3 (x y : K) : xd 19 x * xd 3 y = xd 3 y * xd 19 x :=
  (commute_19_3 x y).eq
theorem tail_19_5 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 5 y * z) = xd 5 y * (xd 19 x * z) :=
  comm_tail (commute_19_5 x y) z
theorem end_19_5 (x y : K) : xd 19 x * xd 5 y = xd 5 y * xd 19 x :=
  (commute_19_5 x y).eq
theorem tail_19_7 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 7 y * z) = xd 7 y * (xd 19 x * z) :=
  comm_tail (commute_19_7 x y) z
theorem end_19_7 (x y : K) : xd 19 x * xd 7 y = xd 7 y * xd 19 x :=
  (commute_19_7 x y).eq
theorem tail_19_9 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 9 y * z) = xd 9 y * (xd 19 x * z) :=
  comm_tail (commute_19_9 x y) z
theorem end_19_9 (x y : K) : xd 19 x * xd 9 y = xd 9 y * xd 19 x :=
  (commute_19_9 x y).eq
theorem tail_19_12 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 12 y * z) = xd 12 y * (xd 19 x * z) :=
  comm_tail (commute_19_12 x y) z
theorem end_19_12 (x y : K) : xd 19 x * xd 12 y = xd 12 y * xd 19 x :=
  (commute_19_12 x y).eq
theorem tail_19_13 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 13 y * z) = xd 13 y * (xd 19 x * z) :=
  comm_tail (commute_19_13 x y) z
theorem end_19_13 (x y : K) : xd 19 x * xd 13 y = xd 13 y * xd 19 x :=
  (commute_19_13 x y).eq
theorem tail_19_15 (x y : K) (z : adjointGroup d4 K) :
    xd 19 x * (xd 15 y * z) = xd 15 y * (xd 19 x * z) :=
  comm_tail (commute_19_15 x y) z
theorem end_19_15 (x y : K) : xd 19 x * xd 15 y = xd 15 y * xd 19 x :=
  (commute_19_15 x y).eq
theorem tail_22_2 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 2 y * z) = xd 2 y * (xd 22 x * z) :=
  comm_tail (commute_22_2 x y) z
theorem end_22_2 (x y : K) : xd 22 x * xd 2 y = xd 2 y * xd 22 x :=
  (commute_22_2 x y).eq
theorem tail_22_0 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 0 y * z) = xd 0 y * (xd 22 x * z) :=
  comm_tail (commute_22_0 x y) z
theorem end_22_0 (x y : K) : xd 22 x * xd 0 y = xd 0 y * xd 22 x :=
  (commute_22_0 x y).eq
theorem tail_22_1 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 1 y * z) = xd 1 y * (xd 22 x * z) :=
  comm_tail (commute_22_1 x y) z
theorem end_22_1 (x y : K) : xd 22 x * xd 1 y = xd 1 y * xd 22 x :=
  (commute_22_1 x y).eq
theorem tail_22_3 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 3 y * z) = xd 3 y * (xd 22 x * z) :=
  comm_tail (commute_22_3 x y) z
theorem end_22_3 (x y : K) : xd 22 x * xd 3 y = xd 3 y * xd 22 x :=
  (commute_22_3 x y).eq
theorem tail_22_5 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 5 y * z) = xd 5 y * (xd 22 x * z) :=
  comm_tail (commute_22_5 x y) z
theorem end_22_5 (x y : K) : xd 22 x * xd 5 y = xd 5 y * xd 22 x :=
  (commute_22_5 x y).eq
theorem tail_22_7 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 7 y * z) = xd 7 y * (xd 22 x * z) :=
  comm_tail (commute_22_7 x y) z
theorem end_22_7 (x y : K) : xd 22 x * xd 7 y = xd 7 y * xd 22 x :=
  (commute_22_7 x y).eq
theorem tail_22_9 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 9 y * z) = xd 9 y * (xd 22 x * z) :=
  comm_tail (commute_22_9 x y) z
theorem end_22_9 (x y : K) : xd 22 x * xd 9 y = xd 9 y * xd 22 x :=
  (commute_22_9 x y).eq
theorem tail_22_12 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 12 y * z) = xd 12 y * (xd 22 x * z) :=
  comm_tail (commute_22_12 x y) z
theorem end_22_12 (x y : K) : xd 22 x * xd 12 y = xd 12 y * xd 22 x :=
  (commute_22_12 x y).eq
theorem tail_22_13 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 13 y * z) = xd 13 y * (xd 22 x * z) :=
  comm_tail (commute_22_13 x y) z
theorem end_22_13 (x y : K) : xd 22 x * xd 13 y = xd 13 y * xd 22 x :=
  (commute_22_13 x y).eq
theorem tail_22_15 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 15 y * z) = xd 15 y * (xd 22 x * z) :=
  comm_tail (commute_22_15 x y) z
theorem end_22_15 (x y : K) : xd 22 x * xd 15 y = xd 15 y * xd 22 x :=
  (commute_22_15 x y).eq
theorem tail_22_19 (x y : K) (z : adjointGroup d4 K) :
    xd 22 x * (xd 19 y * z) = xd 19 y * (xd 22 x * z) :=
  comm_tail (commute_22_19 x y) z
theorem end_22_19 (x y : K) : xd 22 x * xd 19 y = xd 19 y * xd 22 x :=
  (commute_22_19 x y).eq
theorem tail_0_2 (x y : K) (z : adjointGroup d4 K) :
    xd 0 y * (xd 2 x * z) = xd 5 (x * y) * (xd 2 x * (xd 0 y * z)) :=
  swap_tail (swap_0_2 x y) z
theorem end_0_2 (x y : K) :
    xd 0 y * xd 2 x = xd 5 (x * y) * (xd 2 x * xd 0 y) :=
  swap_0_2 x y
theorem tail_1_2 (x y : K) (z : adjointGroup d4 K) :
    xd 1 y * (xd 2 x * z) = xd 7 (x * y) * (xd 2 x * (xd 1 y * z)) :=
  swap_tail (swap_1_2 x y) z
theorem end_1_2 (x y : K) :
    xd 1 y * xd 2 x = xd 7 (x * y) * (xd 2 x * xd 1 y) :=
  swap_1_2 x y
theorem tail_3_2 (x y : K) (z : adjointGroup d4 K) :
    xd 3 y * (xd 2 x * z) = xd 9 (x * y) * (xd 2 x * (xd 3 y * z)) :=
  swap_tail (swap_3_2 x y) z
theorem end_3_2 (x y : K) :
    xd 3 y * xd 2 x = xd 9 (x * y) * (xd 2 x * xd 3 y) :=
  swap_3_2 x y
theorem tail_5_1 (x y : K) (z : adjointGroup d4 K) :
    xd 5 y * (xd 1 x * z) = xd 12 (x * y) * (xd 1 x * (xd 5 y * z)) :=
  swap_tail (swap_5_1 x y) z
theorem end_5_1 (x y : K) :
    xd 5 y * xd 1 x = xd 12 (x * y) * (xd 1 x * xd 5 y) :=
  swap_5_1 x y
theorem tail_5_3 (x y : K) (z : adjointGroup d4 K) :
    xd 5 y * (xd 3 x * z) = xd 13 (x * y) * (xd 3 x * (xd 5 y * z)) :=
  swap_tail (swap_5_3 x y) z
theorem end_5_3 (x y : K) :
    xd 5 y * xd 3 x = xd 13 (x * y) * (xd 3 x * xd 5 y) :=
  swap_5_3 x y
theorem tail_7_0 (x y : K) (z : adjointGroup d4 K) :
    xd 7 y * (xd 0 x * z) = xd 12 (x * y) * (xd 0 x * (xd 7 y * z)) :=
  swap_tail (swap_7_0 x y) z
theorem end_7_0 (x y : K) :
    xd 7 y * xd 0 x = xd 12 (x * y) * (xd 0 x * xd 7 y) :=
  swap_7_0 x y
theorem tail_7_3 (x y : K) (z : adjointGroup d4 K) :
    xd 7 y * (xd 3 x * z) = xd 15 (x * y) * (xd 3 x * (xd 7 y * z)) :=
  swap_tail (swap_7_3 x y) z
theorem end_7_3 (x y : K) :
    xd 7 y * xd 3 x = xd 15 (x * y) * (xd 3 x * xd 7 y) :=
  swap_7_3 x y
theorem tail_9_0 (x y : K) (z : adjointGroup d4 K) :
    xd 9 y * (xd 0 x * z) = xd 13 (x * y) * (xd 0 x * (xd 9 y * z)) :=
  swap_tail (swap_9_0 x y) z
theorem end_9_0 (x y : K) :
    xd 9 y * xd 0 x = xd 13 (x * y) * (xd 0 x * xd 9 y) :=
  swap_9_0 x y
theorem tail_9_1 (x y : K) (z : adjointGroup d4 K) :
    xd 9 y * (xd 1 x * z) = xd 15 (x * y) * (xd 1 x * (xd 9 y * z)) :=
  swap_tail (swap_9_1 x y) z
theorem end_9_1 (x y : K) :
    xd 9 y * xd 1 x = xd 15 (x * y) * (xd 1 x * xd 9 y) :=
  swap_9_1 x y
theorem tail_12_3 (x y : K) (z : adjointGroup d4 K) :
    xd 12 y * (xd 3 x * z) = xd 19 (x * y) * (xd 3 x * (xd 12 y * z)) :=
  swap_tail (swap_12_3 x y) z
theorem end_12_3 (x y : K) :
    xd 12 y * xd 3 x = xd 19 (x * y) * (xd 3 x * xd 12 y) :=
  swap_12_3 x y
theorem tail_12_9 (x y : K) (z : adjointGroup d4 K) :
    xd 12 y * (xd 9 x * z) = xd 22 (x * y) * (xd 9 x * (xd 12 y * z)) :=
  swap_tail (swap_12_9 x y) z
theorem end_12_9 (x y : K) :
    xd 12 y * xd 9 x = xd 22 (x * y) * (xd 9 x * xd 12 y) :=
  swap_12_9 x y
theorem tail_13_1 (x y : K) (z : adjointGroup d4 K) :
    xd 13 y * (xd 1 x * z) = xd 19 (x * y) * (xd 1 x * (xd 13 y * z)) :=
  swap_tail (swap_13_1 x y) z
theorem end_13_1 (x y : K) :
    xd 13 y * xd 1 x = xd 19 (x * y) * (xd 1 x * xd 13 y) :=
  swap_13_1 x y
theorem tail_13_7 (x y : K) (z : adjointGroup d4 K) :
    xd 13 y * (xd 7 x * z) = xd 22 (x * y) * (xd 7 x * (xd 13 y * z)) :=
  swap_tail (swap_13_7 x y) z
theorem end_13_7 (x y : K) :
    xd 13 y * xd 7 x = xd 22 (x * y) * (xd 7 x * xd 13 y) :=
  swap_13_7 x y
theorem tail_15_0 (x y : K) (z : adjointGroup d4 K) :
    xd 15 y * (xd 0 x * z) = xd 19 (x * y) * (xd 0 x * (xd 15 y * z)) :=
  swap_tail (swap_15_0 x y) z
theorem end_15_0 (x y : K) :
    xd 15 y * xd 0 x = xd 19 (x * y) * (xd 0 x * xd 15 y) :=
  swap_15_0 x y
theorem tail_15_5 (x y : K) (z : adjointGroup d4 K) :
    xd 15 y * (xd 5 x * z) = xd 22 (x * y) * (xd 5 x * (xd 15 y * z)) :=
  swap_tail (swap_15_5 x y) z
theorem end_15_5 (x y : K) :
    xd 15 y * xd 5 x = xd 22 (x * y) * (xd 5 x * xd 15 y) :=
  swap_15_5 x y
theorem tail_19_2 (x y : K) (z : adjointGroup d4 K) :
    xd 19 y * (xd 2 x * z) = xd 22 (x * y) * (xd 2 x * (xd 19 y * z)) :=
  swap_tail (swap_19_2 x y) z
theorem end_19_2 (x y : K) :
    xd 19 y * xd 2 x = xd 22 (x * y) * (xd 2 x * xd 19 y) :=
  swap_19_2 x y

end Collection

macro "d4coll" : tactic => `(tactic| simp only [mul_assoc,
    tail_1_0, end_1_0, tail_3_0, end_3_0, tail_3_1, end_3_1, tail_5_2, end_5_2, tail_5_0,
    end_5_0, tail_7_2, end_7_2, tail_7_1, end_7_1, tail_7_5, end_7_5, tail_9_2, end_9_2,
    tail_9_3, end_9_3, tail_9_5, end_9_5, tail_9_7, end_9_7, tail_12_2, end_12_2, tail_12_0,
    end_12_0, tail_12_1, end_12_1, tail_12_5, end_12_5, tail_12_7, end_12_7, tail_13_2,
    end_13_2, tail_13_0, end_13_0, tail_13_3, end_13_3, tail_13_5, end_13_5, tail_13_9,
    end_13_9, tail_13_12, end_13_12, tail_15_2, end_15_2, tail_15_1, end_15_1, tail_15_3,
    end_15_3, tail_15_7, end_15_7, tail_15_9, end_15_9, tail_15_12, end_15_12, tail_15_13,
    end_15_13, tail_19_0, end_19_0, tail_19_1, end_19_1, tail_19_3, end_19_3, tail_19_5,
    end_19_5, tail_19_7, end_19_7, tail_19_9, end_19_9, tail_19_12, end_19_12, tail_19_13,
    end_19_13, tail_19_15, end_19_15, tail_22_2, end_22_2, tail_22_0, end_22_0, tail_22_1,
    end_22_1, tail_22_3, end_22_3, tail_22_5, end_22_5, tail_22_7, end_22_7, tail_22_9,
    end_22_9, tail_22_12, end_22_12, tail_22_13, end_22_13, tail_22_15, end_22_15, tail_22_19,
    end_22_19, tail_0_2, end_0_2, tail_1_2, end_1_2, tail_3_2, end_3_2, tail_5_1, end_5_1,
    tail_5_3, end_5_3, tail_7_0, end_7_0, tail_7_3, end_7_3, tail_9_0, end_9_0, tail_9_1,
    end_9_1, tail_12_3, end_12_3, tail_12_9, end_12_9, tail_13_1, end_13_1, tail_13_7,
    end_13_7, tail_15_0, end_15_0, tail_15_5, end_15_5, tail_19_2, end_19_2,
    xd_merge, xd_merge', xd_cancel, xd_cancel', CharTwo.add_self_eq_zero, xd_zero, one_mul,
    mul_one])

end CFSG.RankThree.PartOne.SEITZ7
