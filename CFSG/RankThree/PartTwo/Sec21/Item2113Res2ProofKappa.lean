module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res2Proof

open Subgroup

variable {G : Type*} [Group G] {c d : G}

@[expose] def kappa (c d : G) (v : ZMod 3 × ZMod 3) : G :=
  c ^ v.1.val * d ^ v.2.val

@[expose] def lin (p q v : ZMod 3 × ZMod 3) : ZMod 3 × ZMod 3 :=
  (v.1 * p.1 + v.2 * q.1, v.1 * p.2 + v.2 * q.2)

theorem pow_mod_three {x : G} (h3 : x ^ 3 = 1) (n : ℕ) : x ^ (n % 3) = x ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h3, one_pow, one_mul]

theorem pow_val_add {x : G} (h3 : x ^ 3 = 1) (a b : ZMod 3) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add, pow_mod_three h3]

theorem kappa_add (h3c : c ^ 3 = 1) (h3d : d ^ 3 = 1) (hcd : Commute c d)
    (v w : ZMod 3 × ZMod 3) : kappa c d (v + w) = kappa c d v * kappa c d w := by
  simp only [kappa, Prod.fst_add, Prod.snd_add, pow_val_add h3c, pow_val_add h3d]
  have h := (hcd.pow_pow w.1.val v.2.val).eq
  calc c ^ v.1.val * c ^ w.1.val * (d ^ v.2.val * d ^ w.2.val) =
      c ^ v.1.val * (c ^ w.1.val * d ^ v.2.val) * d ^ w.2.val := by group
    _ = c ^ v.1.val * (d ^ v.2.val * c ^ w.1.val) * d ^ w.2.val := by rw [h]
    _ = c ^ v.1.val * d ^ v.2.val * (c ^ w.1.val * d ^ w.2.val) := by group

theorem kappa_zero : kappa c d 0 = 1 := by
  simp [kappa]

theorem kappa_one_zero : kappa c d (1, 0) = c := by
  simp [kappa, ZMod.val_one]

theorem kappa_zero_one : kappa c d (0, 1) = d := by
  simp [kappa, ZMod.val_one]

theorem kappa_one_one : kappa c d (1, 1) = c * d := by
  simp [kappa, ZMod.val_one]

theorem kappa_zero_two (h3d : d ^ 3 = 1) : kappa c d (0, 2) = d⁻¹ := by
  have h2 : (2 : ZMod 3).val = 2 := rfl
  simp only [kappa, h2, ZMod.val_zero, pow_zero, one_mul]
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, h3d]

theorem kappa_nsmul (h3c : c ^ 3 = 1) (h3d : d ^ 3 = 1) (hcd : Commute c d) (n : ℕ)
    (v : ZMod 3 × ZMod 3) : kappa c d (n • v) = kappa c d v ^ n := by
  induction n with
  | zero => simp [kappa_zero]
  | succ n ih => rw [succ_nsmul, kappa_add h3c h3d hcd, ih, pow_succ]

theorem kappa_neg (h3c : c ^ 3 = 1) (h3d : d ^ 3 = 1) (hcd : Commute c d)
    (v : ZMod 3 × ZMod 3) : kappa c d (-v) = (kappa c d v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← kappa_add h3c h3d hcd, neg_add_cancel, kappa_zero]

theorem exists_kappa (h3c : c ^ 3 = 1) (h3d : d ^ 3 = 1) (hcd : Commute c d) {y : G}
    (hy : y ∈ closure ({c, d} : Set G)) : ∃ v, kappa c d v = y := by
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ⟨(1, 0), kappa_one_zero⟩
    · exact ⟨(0, 1), kappa_zero_one⟩
  | one => exact ⟨0, kappa_zero⟩
  | mul y z _ _ hy hz =>
    obtain ⟨v, rfl⟩ := hy
    obtain ⟨w, rfl⟩ := hz
    exact ⟨v + w, kappa_add h3c h3d hcd v w⟩
  | inv y _ hy =>
    obtain ⟨v, rfl⟩ := hy
    exact ⟨-v, kappa_neg h3c h3d hcd v⟩

theorem sq_eq_inv_of_cube {x : G} (h3 : x ^ 3 = 1) : x ^ 2 = x⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, h3]

theorem kappa_injective (h3c : c ^ 3 = 1) (h3d : d ^ 3 = 1) (hcd : Commute c d) (hc1 : c ≠ 1)
    (hdc : d ∉ zpowers c) : Function.Injective (kappa c d) := by
  have key : ∀ u : ZMod 3 × ZMod 3, kappa c d u = 1 → u = 0 := by
    have hd1 : d ≠ 1 := fun h => hdc (h ▸ one_mem _)
    have hc2 : c ^ 2 ≠ 1 := by rw [sq_eq_inv_of_cube h3c]; exact inv_ne_one.mpr hc1
    have hd2 : d ^ 2 ≠ 1 := by rw [sq_eq_inv_of_cube h3d]; exact inv_ne_one.mpr hd1
    have hmem : ∀ k : ℕ, c ^ k ∈ zpowers c := fun k => pow_mem (mem_zpowers c) k
    have hd4 : (d ^ 2) ^ 2 = d := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h3d, one_mul, pow_one]
    rintro ⟨u1, u2⟩ h
    simp only [kappa] at h
    suffices hab : u1.val = 0 ∧ u2.val = 0 by
      rw [Prod.mk_eq_zero, ← ZMod.val_eq_zero, ← ZMod.val_eq_zero]
      exact hab
    have ha : u1.val < 3 := ZMod.val_lt u1
    have hb : u2.val < 3 := ZMod.val_lt u2
    generalize u1.val = a at h ha
    generalize u2.val = b at h hb
    interval_cases a <;> interval_cases b <;>
      (try simp only [pow_zero, pow_one, one_mul, mul_one] at h)
    · exact ⟨rfl, rfl⟩
    · exact absurd h hd1
    · exact absurd h hd2
    · exact absurd h hc1
    · exfalso; apply hdc
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem (mem_zpowers c)
    · exfalso; apply hdc
      have h'' : d ^ 2 = c⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [← hd4, h'']
      exact pow_mem (inv_mem (mem_zpowers c)) 2
    · exact absurd h hc2
    · exfalso; apply hdc
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem (hmem 2)
    · exfalso; apply hdc
      have h'' : d ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [← hd4, h'']
      exact pow_mem (inv_mem (hmem 2)) 2
  intro v w h
  have h' : kappa c d (v - w) = 1 := by
    have := kappa_add h3c h3d hcd (v - w) w
    rw [sub_add_cancel, h] at this
    exact (mul_eq_right.mp this.symm)
  exact sub_eq_zero.mp (key _ h')

theorem val_nsmul (a : ZMod 3) (p : ZMod 3 × ZMod 3) : a.val • p = (a * p.1, a * p.2) := by
  ext <;> simp [nsmul_eq_mul]

theorem conj_kappa (h3c : c ^ 3 = 1) (h3d : d ^ 3 = 1) (hcd : Commute c d) {x : G}
    {p q : ZMod 3 × ZMod 3} (hp : x * c * x⁻¹ = kappa c d p) (hq : x * d * x⁻¹ = kappa c d q)
    (v : ZMod 3 × ZMod 3) : x * kappa c d v * x⁻¹ = kappa c d (lin p q v) := by
  have hsplit : x * kappa c d v * x⁻¹ =
      (x * c * x⁻¹) ^ v.1.val * (x * d * x⁻¹) ^ v.2.val := by
    rw [kappa, conj_pow, conj_pow]
    group
  rw [hsplit, hp, hq, ← kappa_nsmul h3c h3d hcd, ← kappa_nsmul h3c h3d hcd,
    ← kappa_add h3c h3d hcd, val_nsmul, val_nsmul]
  rfl

theorem conj_kappa_mul {x y : G} {f g : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3}
    (hx : ∀ v, x * kappa c d v * x⁻¹ = kappa c d (f v))
    (hy : ∀ v, y * kappa c d v * y⁻¹ = kappa c d (g v)) (v : ZMod 3 × ZMod 3) :
    x * y * kappa c d v * (x * y)⁻¹ = kappa c d (f (g v)) := by
  rw [← hx, ← hy]
  group

theorem exists_conj_kappa (h3c : c ^ 3 = 1) (h3d : d ^ 3 = 1) (hcd : Commute c d) {x : G}
    (hx : x ∈ normalizer (closure ({c, d} : Set G) : Set G)) :
    ∃ p q : ZMod 3 × ZMod 3, kappa c d p = x * c * x⁻¹ ∧ kappa c d q = x * d * x⁻¹ ∧
      ∀ v, x * kappa c d v * x⁻¹ = kappa c d (lin p q v) := by
  have hcD : c ∈ closure ({c, d} : Set G) := subset_closure (Set.mem_insert c _)
  have hdD : d ∈ closure ({c, d} : Set G) := subset_closure (Set.mem_insert_of_mem c rfl)
  obtain ⟨p, hp⟩ := exists_kappa h3c h3d hcd ((mem_normalizer_iff.mp hx c).mp hcD)
  obtain ⟨q, hq⟩ := exists_kappa h3c h3d hcd ((mem_normalizer_iff.mp hx d).mp hdD)
  exact ⟨p, q, hp, hq, conj_kappa h3c h3d hcd hp.symm hq.symm⟩

theorem kappa_mem_zpowers_left_iff (h3c : c ^ 3 = 1) (hinj : Function.Injective (kappa c d))
    (v : ZMod 3 × ZMod 3) :
    kappa c d v ∈ zpowers c ↔ v.2 = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have hk' : c ^ k = kappa c d ((k : ZMod 3), 0) := by
      have h3' : c ^ (3 : ℤ) = 1 := by exact_mod_cast h3c
      rw [zpow_eq_zpow_emod k h3']
      have hlt : (k % 3).toNat < 3 := by omega
      have he : k % 3 = ((k % 3).toNat : ℤ) := by omega
      rw [he, zpow_natCast]
      simp only [kappa, ZMod.val_zero, pow_zero, mul_one]
      congr 1
      have h1 := ZMod.val_intCast (n := 3) k
      push_cast at h1
      omega
    rw [hk'] at hk
    exact congrArg Prod.snd (hinj hk.symm)
  · intro h
    obtain ⟨a, b⟩ := v
    simp only at h
    subst h
    simp only [kappa, ZMod.val_zero, pow_zero, mul_one]
    exact pow_mem (mem_zpowers c) _

theorem kappa_mem_zpowers_right_iff (h3d : d ^ 3 = 1) (hinj : Function.Injective (kappa c d))
    (v : ZMod 3 × ZMod 3) :
    kappa c d v ∈ zpowers d ↔ v.1 = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have hk' : d ^ k = kappa c d (0, (k : ZMod 3)) := by
      have h3' : d ^ (3 : ℤ) = 1 := by exact_mod_cast h3d
      rw [zpow_eq_zpow_emod k h3']
      have hlt : (k % 3).toNat < 3 := by omega
      have he : k % 3 = ((k % 3).toNat : ℤ) := by omega
      rw [he, zpow_natCast]
      simp only [kappa, ZMod.val_zero, pow_zero, one_mul]
      congr 1
      have h1 := ZMod.val_intCast (n := 3) k
      push_cast at h1
      omega
    rw [hk'] at hk
    exact congrArg Prod.fst (hinj hk.symm)
  · intro h
    obtain ⟨a, b⟩ := v
    simp only at h
    subst h
    simp only [kappa, ZMod.val_zero, pow_zero, one_mul]
    exact pow_mem (mem_zpowers d) _

end CFSG.RankThree.PartTwo.Sec21.Item2113Res2Proof
