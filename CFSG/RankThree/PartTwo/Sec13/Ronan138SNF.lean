module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mul_pow_three_of_commute {a b : G} (ha : Commute ⁅a, b⁆ a) (hb : Commute ⁅a, b⁆ b) :
    (b * a) ^ 3 = ⁅a, b⁆ ^ 3 * (b ^ 3 * a ^ 3) := by
  set k := ⁅a, b⁆ with hk
  have hab : a * b = k * b * a := by rw [hk, commutatorElement_def]; group
  have hk2 : Commute k (b * b) := hb.mul_right hb
  have hk3 : Commute k (b * b * a) := hk2.mul_right ha
  calc (b * a) ^ 3 = b * (a * b) * (a * b) * a := by rw [pow_three]; group
    _ = b * (k * b * a) * (k * b * a) * a := by rw [hab]
    _ = (b * k) * b * a * k * b * a * a := by group
    _ = (k * b) * b * a * k * b * a * a := by rw [← hb.eq]
    _ = k * (b * b * a * k) * b * a * a := by group
    _ = k * (k * (b * b * a)) * b * a * a := by rw [← hk3.eq]
    _ = k * k * (b * b * (a * b) * a * a) := by group
    _ = k * k * (b * b * (k * b * a) * a * a) := by rw [hab]
    _ = k * k * ((b * b * k) * b * a * a * a) := by group
    _ = k * k * ((k * (b * b)) * b * a * a * a) := by rw [← hk2.eq]
    _ = k ^ 3 * (b ^ 3 * a ^ 3) := by rw [pow_three, pow_three, pow_three]; group

structure HeisFrame (Z : Subgroup G) (x y : G) : Prop where
  x3 : x ^ 3 = 1
  y3 : y ^ 3 = 1
  zx : ∀ z ∈ Z, Commute z x
  zy : ∀ z ∈ Z, Commute z y
  zz : ∀ z ∈ Z, ∀ z' ∈ Z, Commute z z'
  comm_mem : ⁅x, y⁆ ∈ Z
  ind : ∀ i j : ℕ, x ^ i * y ^ j ∈ Z → 3 ∣ i ∧ 3 ∣ j

@[expose] def IsNF (Z : Subgroup G) (x y p : G) (i j : ℕ) : Prop :=
  ∃ z ∈ Z, p = x ^ i * y ^ j * z

variable {Z : Subgroup G} {x y : G}

namespace HeisFrame

variable (h : HeisFrame Z x y)
include h

theorem commute_x : Commute x ⁅x, y⁆ := (h.zx _ h.comm_mem).symm

theorem commute_y : Commute y ⁅x, y⁆ := (h.zy _ h.comm_mem).symm

theorem comm_pow (i j : ℕ) : ⁅x ^ i, y ^ j⁆ = ⁅x, y⁆ ^ (i * j) := by
  rw [pow_mul, h.commute_x.commutatorElement_pow_left i]
  have hy : Commute y ⁅x ^ i, y⁆ := by
    rw [← h.commute_x.commutatorElement_pow_left i]
    exact h.commute_y.pow_right i
  exact (hy.commutatorElement_pow_right j).symm

theorem comm_pow_three : ⁅x, y⁆ ^ 3 = 1 := by
  have h1 := h.comm_pow 1 3
  rw [h.y3, commutatorElement_one_right, one_mul] at h1
  exact h1.symm

theorem pow_mul_pow_swap (i j : ℕ) :
    y ^ j * x ^ i = (⁅x, y⁆ ^ (i * j))⁻¹ * (x ^ i * y ^ j) := by
  have h1 := h.comm_pow i j
  rw [commutatorElement_def] at h1
  rw [← h1]
  group

end HeisFrame

namespace IsNF

variable (h : HeisFrame Z x y)
include h

theorem of_mem {z : G} (hz : z ∈ Z) : IsNF Z x y z 0 0 := ⟨z, hz, by simp⟩

omit h in
theorem one : IsNF Z x y 1 0 0 := ⟨1, one_mem _, by simp⟩

omit h in
theorem gen_x : IsNF Z x y x 1 0 := ⟨1, one_mem _, by simp⟩

omit h in
theorem gen_y : IsNF Z x y y 0 1 := ⟨1, one_mem _, by simp⟩

theorem mul {p q : G} {i j k l : ℕ} (hp : IsNF Z x y p i j) (hq : IsNF Z x y q k l) :
    IsNF Z x y (p * q) (i + k) (j + l) := by
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨z', hz', rfl⟩ := hq
  set D := (⁅x, y⁆ ^ (k * j))⁻¹ with hD
  have hDZ : D ∈ Z := inv_mem (pow_mem h.comm_mem _)
  refine ⟨D * z * z', mul_mem (mul_mem hDZ hz) hz', ?_⟩
  have hzc : Commute z (x ^ k * y ^ l) :=
    ((h.zx z hz).pow_right k).mul_right ((h.zy z hz).pow_right l)
  have hDx : Commute D (x ^ i) := (h.zx D hDZ).pow_right i
  have hDx' : Commute D (x ^ k) := (h.zx D hDZ).pow_right k
  have hDy : Commute D (y ^ (j + l)) := (h.zy D hDZ).pow_right _
  have hsw := h.pow_mul_pow_swap k j
  calc x ^ i * y ^ j * z * (x ^ k * y ^ l * z') =
      x ^ i * y ^ j * (z * (x ^ k * y ^ l)) * z' := by group
    _ = x ^ i * y ^ j * (x ^ k * y ^ l * z) * z' := by rw [hzc.eq]
    _ = x ^ i * (y ^ j * x ^ k) * y ^ l * (z * z') := by group
    _ = x ^ i * (D * (x ^ k * y ^ j)) * y ^ l * (z * z') := by rw [hsw]
    _ = (x ^ i * D) * x ^ k * (y ^ j * y ^ l) * (z * z') := by group
    _ = (D * x ^ i) * x ^ k * (y ^ j * y ^ l) * (z * z') := by rw [hDx.eq]
    _ = D * (x ^ i * x ^ k) * (y ^ j * y ^ l) * (z * z') := by group
    _ = D * (x ^ (i + k) * y ^ (j + l)) * (z * z') := by rw [← pow_add, ← pow_add]; group
    _ = (D * x ^ (i + k)) * y ^ (j + l) * (z * z') := by group
    _ = (x ^ (i + k) * D) * y ^ (j + l) * (z * z') := by
        rw [((h.zx D hDZ).pow_right (i + k)).eq]
    _ = x ^ (i + k) * (D * y ^ (j + l)) * (z * z') := by group
    _ = x ^ (i + k) * (y ^ (j + l) * D) * (z * z') := by rw [hDy.eq]
    _ = x ^ (i + k) * y ^ (j + l) * (D * z * z') := by group

theorem pow {p : G} {i j : ℕ} (hp : IsNF Z x y p i j) (n : ℕ) :
    IsNF Z x y (p ^ n) (i * n) (j * n) := by
  induction n with
  | zero => simpa using one (Z := Z) (x := x) (y := y)
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ, Nat.mul_succ]
    exact mul h ih hp

theorem inv {p : G} {i j : ℕ} (hp : IsNF Z x y p i j) : IsNF Z x y p⁻¹ (2 * i) (2 * j) := by
  obtain ⟨z, hz, rfl⟩ := hp
  have hx : (x ^ i)⁻¹ = x ^ (2 * i) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, h.x3, one_pow]
  have hy : (y ^ j)⁻¹ = y ^ (2 * j) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, h.y3, one_pow]
  have h1 : (x ^ i * y ^ j * z)⁻¹ = z⁻¹ * (y ^ (2 * j) * x ^ (2 * i)) := by
    rw [mul_inv_rev, mul_inv_rev, hx, hy]
  rw [h1]
  have h2 : IsNF Z x y (y ^ (2 * j) * x ^ (2 * i)) (0 + 2 * i) (2 * j + 0) := by
    refine mul h ?_ ?_
    · simpa using pow h gen_y (2 * j)
    · simpa using pow h gen_x (2 * i)
  have h3 := mul h (of_mem h (inv_mem hz)) h2
  simpa using h3

theorem unique {p : G} {i j k l : ℕ} (hp : IsNF Z x y p i j) (hq : IsNF Z x y p k l) :
    (i : ZMod 3) = k ∧ (j : ZMod 3) = l := by
  have h1 := mul h hp (inv h hq)
  rw [mul_inv_cancel] at h1
  obtain ⟨z, hz, hz1⟩ := h1
  have h2 : x ^ (i + 2 * k) * y ^ (j + 2 * l) ∈ Z := by
    have : x ^ (i + 2 * k) * y ^ (j + 2 * l) = z⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hz1]
    rw [this]
    exact inv_mem hz
  obtain ⟨h3, h4⟩ := h.ind _ _ h2
  have key : ∀ a b : ZMod 3, a + 2 * b = 0 → a = b := by decide
  constructor
  · have := (ZMod.natCast_eq_zero_iff (i + 2 * k) 3).mpr h3
    push_cast at this
    exact key _ _ this
  · have := (ZMod.natCast_eq_zero_iff (j + 2 * l) 3).mpr h4
    push_cast at this
    exact key _ _ this

theorem mem_iff {p : G} {i j : ℕ} (hp : IsNF Z x y p i j) :
    p ∈ Z ↔ (i : ZMod 3) = 0 ∧ (j : ZMod 3) = 0 := by
  constructor
  · intro hpZ
    have := unique h hp (of_mem h hpZ)
    simpa using this
  · rintro ⟨hi, hj⟩
    obtain ⟨z, hz, rfl⟩ := hp
    have hi' : 3 ∣ i := (ZMod.natCast_eq_zero_iff i 3).mp hi
    have hj' : 3 ∣ j := (ZMod.natCast_eq_zero_iff j 3).mp hj
    obtain ⟨a, rfl⟩ := hi'
    obtain ⟨b, rfl⟩ := hj'
    rw [pow_mul, pow_mul, h.x3, h.y3, one_pow, one_pow, one_mul, one_mul]
    exact hz

theorem conj {u : G} (hu : ∀ z ∈ Z, u * z * u⁻¹ ∈ Z) {a b a' b' : ℕ}
    (hx : IsNF Z x y (u * x * u⁻¹) a b) (hy : IsNF Z x y (u * y * u⁻¹) a' b')
    {p : G} {i j : ℕ} (hp : IsNF Z x y p i j) :
    IsNF Z x y (u * p * u⁻¹) (a * i + a' * j) (b * i + b' * j) := by
  obtain ⟨z, hz, rfl⟩ := hp
  have e1 : u * (x ^ i * y ^ j * z) * u⁻¹ =
      (u * x * u⁻¹) ^ i * (u * y * u⁻¹) ^ j * (u * z * u⁻¹) := by
    rw [conj_pow, conj_pow]
    group
  rw [e1]
  have h1 := mul h (mul h (pow h hx i) (pow h hy j)) (of_mem h (hu z hz))
  simpa using h1

theorem commutator {p q : G} {a b a' b' : ℕ} (hp : IsNF Z x y p a b) (hq : IsNF Z x y q a' b') :
    ⁅p, q⁆ = ⁅x, y⁆ ^ (a * b' + 2 * a' * b) := by
  obtain ⟨z, hz, rfl⟩ := hp
  obtain ⟨z', hz', rfl⟩ := hq
  set d := ⁅x, y⁆ with hd
  have hdZ : d ∈ Z := h.comm_mem
  have hpq : x ^ a * y ^ b * z * (x ^ a' * y ^ b' * z') =
      x ^ (a + a') * y ^ (b + b') * ((d ^ (a' * b))⁻¹ * z * z') := by
    have hzc : Commute z (x ^ a' * y ^ b') :=
      ((h.zx z hz).pow_right a').mul_right ((h.zy z hz).pow_right b')
    have hsw := h.pow_mul_pow_swap a' b
    set D := (d ^ (a' * b))⁻¹ with hD
    have hDZ : D ∈ Z := inv_mem (pow_mem hdZ _)
    have hDx : Commute D (x ^ a) := (h.zx D hDZ).pow_right a
    have hDy : Commute D (y ^ (b + b')) := (h.zy D hDZ).pow_right _
    calc x ^ a * y ^ b * z * (x ^ a' * y ^ b' * z') =
        x ^ a * y ^ b * (z * (x ^ a' * y ^ b')) * z' := by group
      _ = x ^ a * y ^ b * (x ^ a' * y ^ b' * z) * z' := by rw [hzc.eq]
      _ = x ^ a * (y ^ b * x ^ a') * y ^ b' * (z * z') := by group
      _ = x ^ a * (D * (x ^ a' * y ^ b)) * y ^ b' * (z * z') := by rw [hsw]
      _ = (x ^ a * D) * x ^ a' * (y ^ b * y ^ b') * (z * z') := by group
      _ = (D * x ^ a) * x ^ a' * (y ^ b * y ^ b') * (z * z') := by rw [hDx.eq]
      _ = D * (x ^ a * x ^ a') * (y ^ b * y ^ b') * (z * z') := by group
      _ = D * (x ^ (a + a') * y ^ (b + b')) * (z * z') := by rw [← pow_add, ← pow_add]; group
      _ = (D * x ^ (a + a')) * y ^ (b + b') * (z * z') := by group
      _ = (x ^ (a + a') * D) * y ^ (b + b') * (z * z') := by
          rw [((h.zx D hDZ).pow_right (a + a')).eq]
      _ = x ^ (a + a') * (D * y ^ (b + b')) * (z * z') := by group
      _ = x ^ (a + a') * (y ^ (b + b') * D) * (z * z') := by rw [hDy.eq]
      _ = x ^ (a + a') * y ^ (b + b') * (D * z * z') := by group
  have hqp : x ^ a' * y ^ b' * z' * (x ^ a * y ^ b * z) =
      x ^ (a + a') * y ^ (b + b') * ((d ^ (a * b'))⁻¹ * z * z') := by
    have hzc : Commute z' (x ^ a * y ^ b) :=
      ((h.zx z' hz').pow_right a).mul_right ((h.zy z' hz').pow_right b)
    have hsw := h.pow_mul_pow_swap a b'
    set D := (d ^ (a * b'))⁻¹ with hD
    have hDZ : D ∈ Z := inv_mem (pow_mem hdZ _)
    have hDx : Commute D (x ^ a') := (h.zx D hDZ).pow_right a'
    have hDy : Commute D (y ^ (b + b')) := (h.zy D hDZ).pow_right _
    have hzz : Commute z' z := h.zz z' hz' z hz
    calc x ^ a' * y ^ b' * z' * (x ^ a * y ^ b * z) =
        x ^ a' * y ^ b' * (z' * (x ^ a * y ^ b)) * z := by group
      _ = x ^ a' * y ^ b' * (x ^ a * y ^ b * z') * z := by rw [hzc.eq]
      _ = x ^ a' * (y ^ b' * x ^ a) * y ^ b * (z' * z) := by group
      _ = x ^ a' * (D * (x ^ a * y ^ b')) * y ^ b * (z' * z) := by rw [hsw]
      _ = (x ^ a' * D) * x ^ a * (y ^ b' * y ^ b) * (z' * z) := by group
      _ = (D * x ^ a') * x ^ a * (y ^ b' * y ^ b) * (z' * z) := by rw [hDx.eq]
      _ = D * (x ^ a' * x ^ a) * (y ^ b' * y ^ b) * (z' * z) := by group
      _ = D * (x ^ (a + a') * y ^ (b + b')) * (z * z') := by
          rw [← pow_add, ← pow_add, add_comm a' a, add_comm b' b, hzz.eq]; group
      _ = (D * x ^ (a + a')) * y ^ (b + b') * (z * z') := by group
      _ = (x ^ (a + a') * D) * y ^ (b + b') * (z * z') := by
          rw [((h.zx D hDZ).pow_right (a + a')).eq]
      _ = x ^ (a + a') * (D * y ^ (b + b')) * (z * z') := by group
      _ = x ^ (a + a') * (y ^ (b + b') * D) * (z * z') := by rw [hDy.eq]
      _ = x ^ (a + a') * y ^ (b + b') * (D * z * z') := by group
  have hcomm : ⁅x ^ a * y ^ b * z, x ^ a' * y ^ b' * z'⁆ =
      (x ^ a * y ^ b * z * (x ^ a' * y ^ b' * z')) *
        (x ^ a' * y ^ b' * z' * (x ^ a * y ^ b * z))⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hcomm, hpq, hqp]
  set X := x ^ (a + a') * y ^ (b + b') with hX
  set W := z * z' with hW
  have e1 : (d ^ (a' * b))⁻¹ * z * z' = (d ^ (a' * b))⁻¹ * W := by rw [hW, mul_assoc]
  have e2 : (d ^ (a * b'))⁻¹ * z * z' = (d ^ (a * b'))⁻¹ * W := by rw [hW, mul_assoc]
  rw [e1, e2]
  calc X * ((d ^ (a' * b))⁻¹ * W) * (X * ((d ^ (a * b'))⁻¹ * W))⁻¹ =
      X * ((d ^ (a' * b))⁻¹ * W) * (((d ^ (a * b'))⁻¹ * W)⁻¹ * X⁻¹) := by group
    _ = X * (((d ^ (a' * b))⁻¹ * W) * ((d ^ (a * b'))⁻¹ * W)⁻¹) * X⁻¹ := by group
    _ = X * ((d ^ (a' * b))⁻¹ * d ^ (a * b')) * X⁻¹ := by group
    _ = (d ^ (a' * b))⁻¹ * d ^ (a * b') := by
        have hc : (d ^ (a' * b))⁻¹ * d ^ (a * b') ∈ Z :=
          mul_mem (inv_mem (pow_mem hdZ _)) (pow_mem hdZ _)
        have hXc' : Commute X ((d ^ (a' * b))⁻¹ * d ^ (a * b')) :=
          (((h.zx _ hc).pow_right (a + a')).mul_right ((h.zy _ hc).pow_right (b + b'))).symm
        rw [hXc'.eq, mul_inv_cancel_right]
    _ = d ^ (a * b' + 2 * a' * b) := by
        have h3 : d ^ 3 = 1 := h.comm_pow_three
        have hinv : (d ^ (a' * b))⁻¹ = d ^ (2 * a' * b) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show a' * b + 2 * a' * b = 3 * (a' * b) by ring,
            pow_mul, h3, one_pow]
        rw [hinv, ← pow_add, add_comm (2 * a' * b)]

end IsNF

theorem zmod3_of_sq : ∀ a b a' b' : ZMod 3, a * b' + 2 * a' * b = 2 → b ≠ 0 →
    a' * (a + b') = 0 → a' = 0 ∨ a = 0 := by
  decide

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
