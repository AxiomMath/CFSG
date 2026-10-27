module

public import CFSG.RankThree.Native.LyFiveTheory
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Std.Tactic.BVDecide.Normalize.Prop

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem card_kernel (l : Fin 4 → ZMod 3) (hl : l ≠ 0) :
    (Finset.univ.filter fun e : Fin 4 → ZMod 3 => ∑ j, l j * e j = 0).card = 27 := by
  revert l
  decide

@[expose] def threeNF (x : G) (v : Fin 4 → G) (c : ZMod 3) (e : Fin 4 → ZMod 3) : G :=
  v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val * x ^ c.val

@[expose] def threeQ (x : G) (v : Fin 4 → G) : Subgroup G := closure (insert x (Set.range v))

structure ThreeQRel (x : G) (v : Fin 4 → G) (ω : Fin 4 → Fin 4 → ZMod 3) : Prop where
  xcube : x ^ 3 = 1
  x1 : x ≠ 1
  vcube : ∀ i, v i ^ 3 = 1
  xv : ∀ i, x * v i = v i * x
  comm : ∀ i j, ⁅v i, v j⁆ = x ^ (ω i j).val
  nondeg : ∀ e : Fin 4 → ZMod 3, (∀ j, ∑ i, e i * ω i j = 0) → e = 0

theorem pow_mod_three {g : G} (hg : g ^ 3 = 1) (n : ℕ) : g ^ (n % 3) = g ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hg, one_pow, one_mul]

theorem zmod3_val_add_one (a : ZMod 3) : (a + 1).val = (a.val + 1) % 3 := by
  revert a; decide

namespace ThreeQRel

variable {x : G} {v : Fin 4 → G} {ω : Fin 4 → Fin 4 → ZMod 3}

theorem x_mem : x ∈ threeQ x v := subset_closure (Set.mem_insert _ _)

theorem v_mem (i : Fin 4) : v i ∈ threeQ x v :=
  subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

theorem pow_mem {g : G} (hg : g ∈ threeQ x v) (n : ℕ) : g ^ n ∈ threeQ x v :=
  Subgroup.pow_mem _ hg n

variable (h : ThreeQRel x v ω)
include h

theorem orderOf_x : orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime h.xcube h.x1

theorem x_pow_eq_one_iff (n : ℕ) : x ^ n = 1 ↔ (n : ZMod 3) = 0 := by
  rw [← orderOf_dvd_iff_pow_eq_one, h.orderOf_x, ZMod.natCast_eq_zero_iff]

theorem x_comm {g : G} (hg : g ∈ threeQ x v) : Commute x g := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨i, rfl⟩
    · exact Commute.refl _
    · exact h.xv i
  | one => exact Commute.one_right _
  | mul _ _ _ _ h1 h2 => exact h1.mul_right h2
  | inv _ _ h1 => exact h1.inv_right

theorem zpowers_comm {z g : G} (hz : z ∈ zpowers x) (hg : g ∈ threeQ x v) : Commute z g := by
  obtain ⟨k, rfl⟩ := hz
  exact (h.x_comm hg).zpow_left k

theorem comm_gen_mem {g : G} (hg : g ∈ threeQ x v) {s : G} (hs : s ∈ insert x (Set.range v)) :
    ⁅g, s⁆ ∈ zpowers x := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | ⟨i, rfl⟩ <;> rcases hs with rfl | ⟨j, rfl⟩
    · rw [commutatorElement_self]; exact one_mem _
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (h.xv j)]; exact one_mem _
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (h.xv i).symm]; exact one_mem _
    · rw [h.comm i j]; exact npow_mem_zpowers x _
  | one => rw [commutatorElement_one_left]; exact one_mem _
  | mul a b ha hb iha ihb =>
    rw [commutator_mul_left_of_commute (h.zpowers_comm ihb ha)]
    exact mul_mem ihb iha
  | inv a ha iha =>
    rw [commutator_inv_left_of_commute (h.zpowers_comm iha ha)]
    exact inv_mem iha

theorem comm_mem {g k : G} (hg : g ∈ threeQ x v) (hk : k ∈ threeQ x v) : ⁅g, k⁆ ∈ zpowers x := by
  induction hk using Subgroup.closure_induction with
  | mem s hs => exact h.comm_gen_mem hg hs
  | one => rw [commutatorElement_one_right]; exact one_mem _
  | mul a b ha hb iha ihb =>
    rw [commutator_mul_right_of_commute (h.zpowers_comm ihb ha)]
    exact mul_mem iha ihb
  | inv a ha iha =>
    rw [commutator_inv_right_of_commute (h.zpowers_comm iha ha)]
    exact inv_mem iha

theorem comm_comm {g k m : G} (hg : g ∈ threeQ x v) (hk : k ∈ threeQ x v)
    (hm : m ∈ threeQ x v) : Commute ⁅g, k⁆ m :=
  h.zpowers_comm (h.comm_mem hg hk) hm

omit h in
theorem nf_mem (c : ZMod 3) (e : Fin 4 → ZMod 3) : threeNF x v c e ∈ threeQ x v := by
  unfold threeNF
  exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (v_mem 3) _) (pow_mem (v_mem 2) _))
    (pow_mem (v_mem 1) _)) (pow_mem (v_mem 0) _)) (pow_mem x_mem _)

theorem comm_v_pow (i j : Fin 4) (n : ℕ) : ⁅v i ^ n, v j⁆ = x ^ ((ω i j).val * n) := by
  rw [commutator_pow_left_of_commute (h.comm_comm (v_mem (x := x) i) (v_mem j) (v_mem i)), h.comm,
    pow_mul]

theorem comm_x_pow (n : ℕ) (j : Fin 4) : ⁅x ^ n, v j⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact ((h.x_comm (v_mem (x := x) j)).pow_left n).eq

theorem comm_nf (c : ZMod 3) (e : Fin 4 → ZMod 3) (j : Fin 4) :
    ⁅threeNF x v c e, v j⁆ =
      x ^ ((ω 0 j).val * (e 0).val + (ω 1 j).val * (e 1).val + (ω 2 j).val * (e 2).val +
        (ω 3 j).val * (e 3).val) := by
  have hm : ∀ {g s : G}, g ∈ threeQ x v → s ∈ threeQ x v → ∀ k ∈ threeQ x v,
      Commute ⁅g, s⁆ k := fun hg hs k hk => h.comm_comm hg hs hk
  have hv : ∀ i, v i ∈ threeQ x v := fun i => v_mem i
  have hvj := hv j
  have h3 := pow_mem (hv 3) (e 3).val
  have h2 := pow_mem (hv 2) (e 2).val
  have h1 := pow_mem (hv 1) (e 1).val
  have h0 := pow_mem (hv 0) (e 0).val
  have hx := pow_mem (x_mem (x := x) (v := v)) c.val
  unfold threeNF
  rw [commutator_mul_left_of_commute (hm hx hvj _ (mul_mem (mul_mem (mul_mem h3 h2) h1) h0)),
    h.comm_x_pow, one_mul,
    commutator_mul_left_of_commute (hm h0 hvj _ (mul_mem (mul_mem h3 h2) h1)),
    commutator_mul_left_of_commute (hm h1 hvj _ (mul_mem h3 h2)),
    commutator_mul_left_of_commute (hm h2 hvj _ h3),
    h.comm_v_pow, h.comm_v_pow, h.comm_v_pow, h.comm_v_pow, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

theorem comm_nf_eq_one_iff (c : ZMod 3) (e : Fin 4 → ZMod 3) (j : Fin 4) :
    ⁅threeNF x v c e, v j⁆ = 1 ↔ ∑ i, e i * ω i j = 0 := by
  rw [h.comm_nf, h.x_pow_eq_one_iff, Fin.sum_univ_four]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  constructor <;> intro hs <;> linear_combination hs

theorem coord_eq_of_comm {c c' : ZMod 3} {e e' : Fin 4 → ZMod 3}
    (hcomm : ∀ j, ⁅threeNF x v c e, v j⁆ = ⁅threeNF x v c' e', v j⁆) : e = e' := by
  have hd : e - e' = 0 := by
    apply h.nondeg
    intro j
    have hj := hcomm j
    rw [h.comm_nf, h.comm_nf] at hj
    have h3 := h.orderOf_x
    have := (pow_eq_pow_iff_modEq.1 hj)
    rw [h3] at this
    have hz := (ZMod.natCast_eq_natCast_iff _ _ 3).2 this
    push_cast at hz
    simp only [ZMod.natCast_val, ZMod.cast_id', id] at hz
    simp only [Pi.sub_apply, sub_mul, Fin.sum_univ_four]
    linear_combination hz
  exact sub_eq_zero.1 hd

theorem xpow_comm (k : ℕ) {g : G} (hg : g ∈ threeQ x v) : x ^ k * g = g * x ^ k :=
  ((h.x_comm hg).pow_left k).eq

theorem xpow_mul_nf (m : ℕ) (c : ZMod 3) (e : Fin 4 → ZMod 3) :
    x ^ m * threeNF x v c e = threeNF x v (c + m) e := by
  have hv : ∀ i, v i ∈ threeQ x v := fun i => v_mem i
  have hP : v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val ∈ threeQ x v :=
    mul_mem (mul_mem (mul_mem (pow_mem (hv 3) _) (pow_mem (hv 2) _)) (pow_mem (hv 1) _))
      (pow_mem (hv 0) _)
  unfold threeNF
  rw [← mul_assoc, h.xpow_comm m hP, mul_assoc, ← pow_add, ZMod.val_add, ZMod.val_natCast,
    Nat.add_mod_mod, pow_mod_three h.xcube, Nat.add_comm]

theorem v_mul_vpow (i j : Fin 4) (a : ℕ) :
    v i * v j ^ a = x ^ ((ω i j).val * a) * v j ^ a * v i := by
  rw [mul_eq_commutator_mul, commutator_pow_right_of_commute
    (h.comm_comm (v_mem (x := x) i) (v_mem j) (v_mem j)), h.comm, ← pow_mul]

@[expose] def threeBump (e : Fin 4 → ZMod 3) (i : Fin 4) : Fin 4 → ZMod 3 :=
  fun k => if k = i then e k + 1 else e k

omit h in
theorem single_val (i k : Fin 4) (e : Fin 4 → ZMod 3) :
    (threeBump e i k).val = if k = i then ((e k).val + 1) % 3 else (e k).val := by
  unfold threeBump
  split_ifs
  · exact zmod3_val_add_one _
  · rfl

theorem v3_mul_nf (c : ZMod 3) (e : Fin 4 → ZMod 3) :
    v 3 * threeNF x v c e = threeNF x v c (threeBump e 3) := by
  unfold threeNF
  rw [single_val, single_val, single_val, single_val]
  simp only [show (2 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 3 by decide,
    show (0 : Fin 4) ≠ 3 by decide, ite_true, ite_false]
  rw [pow_mod_three (h.vcube 3), pow_succ']
  simp only [mul_assoc]

theorem v2_mul_nf (c : ZMod 3) (e : Fin 4 → ZMod 3) :
    ∃ c', v 2 * threeNF x v c e = threeNF x v c' (threeBump e 2) := by
  refine ⟨c + ((ω 2 3).val * (e 3).val : ℕ), ?_⟩
  rw [← h.xpow_mul_nf]
  unfold threeNF
  rw [single_val, single_val, single_val, single_val]
  simp only [show (3 : Fin 4) ≠ 2 by decide, show (1 : Fin 4) ≠ 2 by decide,
    show (0 : Fin 4) ≠ 2 by decide, ite_true, ite_false]
  rw [pow_mod_three (h.vcube 2)]
  calc v 2 * (v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val *
        x ^ c.val) = (v 2 * v 3 ^ (e 3).val) * v 2 ^ (e 2).val * v 1 ^ (e 1).val *
          v 0 ^ (e 0).val * x ^ c.val := by simp only [mul_assoc]
    _ = _ := by
        rw [h.v_mul_vpow, pow_succ' (v 2)]
        simp only [mul_assoc]

theorem v1_mul_nf (c : ZMod 3) (e : Fin 4 → ZMod 3) :
    ∃ c', v 1 * threeNF x v c e = threeNF x v c' (threeBump e 1) := by
  refine ⟨c + ((ω 1 3).val * (e 3).val + (ω 1 2).val * (e 2).val : ℕ), ?_⟩
  rw [← h.xpow_mul_nf]
  unfold threeNF
  rw [single_val, single_val, single_val, single_val]
  simp only [show (3 : Fin 4) ≠ 1 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (0 : Fin 4) ≠ 1 by decide, ite_true, ite_false]
  rw [pow_mod_three (h.vcube 1)]
  have h3 : v 3 ^ (e 3).val ∈ threeQ x v := pow_mem (v_mem 3) _
  calc v 1 * (v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val *
        x ^ c.val) = (v 1 * v 3 ^ (e 3).val) * v 2 ^ (e 2).val * v 1 ^ (e 1).val *
          v 0 ^ (e 0).val * x ^ c.val := by simp only [mul_assoc]
    _ = x ^ ((ω 1 3).val * (e 3).val) * v 3 ^ (e 3).val * (v 1 * v 2 ^ (e 2).val) *
          v 1 ^ (e 1).val * v 0 ^ (e 0).val * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = x ^ ((ω 1 3).val * (e 3).val) * (v 3 ^ (e 3).val * x ^ ((ω 1 2).val * (e 2).val)) *
          v 2 ^ (e 2).val * (v 1 * v 1 ^ (e 1).val) * v 0 ^ (e 0).val * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = _ := by
        rw [← h.xpow_comm _ h3, ← pow_succ' (v 1),
          pow_add x ((ω 1 3).val * (e 3).val) ((ω 1 2).val * (e 2).val)]
        simp only [mul_assoc]

theorem v0_mul_nf (c : ZMod 3) (e : Fin 4 → ZMod 3) :
    ∃ c', v 0 * threeNF x v c e = threeNF x v c' (threeBump e 0) := by
  refine ⟨c + ((ω 0 3).val * (e 3).val + (ω 0 2).val * (e 2).val +
    (ω 0 1).val * (e 1).val : ℕ), ?_⟩
  rw [← h.xpow_mul_nf]
  unfold threeNF
  rw [single_val, single_val, single_val, single_val]
  simp only [show (3 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (1 : Fin 4) ≠ 0 by decide, ite_true, ite_false]
  rw [pow_mod_three (h.vcube 0)]
  have h3 : v 3 ^ (e 3).val ∈ threeQ x v := pow_mem (v_mem 3) _
  have h2 : v 2 ^ (e 2).val ∈ threeQ x v := pow_mem (v_mem 2) _
  calc v 0 * (v 3 ^ (e 3).val * v 2 ^ (e 2).val * v 1 ^ (e 1).val * v 0 ^ (e 0).val *
        x ^ c.val) = (v 0 * v 3 ^ (e 3).val) * v 2 ^ (e 2).val * v 1 ^ (e 1).val *
          v 0 ^ (e 0).val * x ^ c.val := by simp only [mul_assoc]
    _ = x ^ ((ω 0 3).val * (e 3).val) * v 3 ^ (e 3).val * (v 0 * v 2 ^ (e 2).val) *
          v 1 ^ (e 1).val * v 0 ^ (e 0).val * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = x ^ ((ω 0 3).val * (e 3).val) * (v 3 ^ (e 3).val * x ^ ((ω 0 2).val * (e 2).val)) *
          v 2 ^ (e 2).val * (v 0 * v 1 ^ (e 1).val) * v 0 ^ (e 0).val * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = x ^ ((ω 0 3).val * (e 3).val) * (v 3 ^ (e 3).val * x ^ ((ω 0 2).val * (e 2).val)) *
          (v 2 ^ (e 2).val * x ^ ((ω 0 1).val * (e 1).val)) * v 1 ^ (e 1).val *
          (v 0 * v 0 ^ (e 0).val) * x ^ c.val := by
        rw [h.v_mul_vpow]; simp only [mul_assoc]
    _ = _ := by
        rw [← h.xpow_comm _ h3, ← h.xpow_comm _ h2,
          show x ^ ((ω 0 3).val * (e 3).val) * (x ^ ((ω 0 2).val * (e 2).val) * v 3 ^ (e 3).val) *
            (x ^ ((ω 0 1).val * (e 1).val) * v 2 ^ (e 2).val) * v 1 ^ (e 1).val *
            (v 0 * v 0 ^ (e 0).val) * x ^ c.val =
            x ^ ((ω 0 3).val * (e 3).val) * x ^ ((ω 0 2).val * (e 2).val) *
            (v 3 ^ (e 3).val * x ^ ((ω 0 1).val * (e 1).val)) * v 2 ^ (e 2).val *
            v 1 ^ (e 1).val * (v 0 * v 0 ^ (e 0).val) * x ^ c.val by simp only [mul_assoc],
          ← h.xpow_comm _ h3, ← pow_succ' (v 0),
          pow_add x ((ω 0 3).val * (e 3).val + (ω 0 2).val * (e 2).val)
            ((ω 0 1).val * (e 1).val),
          pow_add x ((ω 0 3).val * (e 3).val) ((ω 0 2).val * (e 2).val)]
        simp only [mul_assoc]

omit h in
theorem gen_pow_three' (h5 : ThreeQRel x v ω) {s : G} (hs : s ∈ insert x (Set.range v)) :
    s ^ 3 = 1 := by
  rcases hs with rfl | ⟨i, rfl⟩
  · exact h5.xcube
  · exact h5.vcube i

theorem gen_mul_nf {s : G} (hs : s ∈ insert x (Set.range v)) (c : ZMod 3)
    (e : Fin 4 → ZMod 3) : ∃ c' e', s * threeNF x v c e = threeNF x v c' e' := by
  rcases hs with rfl | ⟨i, rfl⟩
  · exact ⟨c + ((1 : ℕ) : ZMod 3), e, by rw [← h.xpow_mul_nf, pow_one]⟩
  · match i with
    | 0 => obtain ⟨c', hc⟩ := h.v0_mul_nf c e; exact ⟨c', _, hc⟩
    | 1 => obtain ⟨c', hc⟩ := h.v1_mul_nf c e; exact ⟨c', _, hc⟩
    | 2 => obtain ⟨c', hc⟩ := h.v2_mul_nf c e; exact ⟨c', _, hc⟩
    | 3 => exact ⟨c, _, h.v3_mul_nf c e⟩

omit h in
theorem nf_zero : threeNF x v 0 0 = 1 := by simp [threeNF]

theorem mem_range_nf {g : G} (hg : g ∈ threeQ x v) : ∃ c e, g = threeNF x v c e := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, 0, nf_zero.symm⟩
  | mul_left s hs y _ ih =>
    obtain ⟨c, e, rfl⟩ := ih
    obtain ⟨c', e', he⟩ := h.gen_mul_nf hs c e
    exact ⟨c', e', he⟩
  | inv_mul_cancel s hs y _ ih =>
    obtain ⟨c, e, rfl⟩ := ih
    have hinv : s⁻¹ = s * s := by
      rw [inv_eq_iff_mul_eq_one, ← h.gen_pow_three' hs]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    obtain ⟨c1, e1, h1⟩ := h.gen_mul_nf hs c e
    obtain ⟨c2, e2, h2⟩ := h.gen_mul_nf hs c1 e1
    exact ⟨c2, e2, by rw [hinv, mul_assoc, h1, h2]⟩

theorem nf_injective :
    Function.Injective fun p : ZMod 3 × (Fin 4 → ZMod 3) => threeNF x v p.1 p.2 := by
  rintro ⟨c, e⟩ ⟨c', e'⟩ hEq
  simp only at hEq
  have he : e = e' := h.coord_eq_of_comm fun j => by rw [hEq]
  subst he
  have hx : x ^ c.val = x ^ c'.val := by
    unfold threeNF at hEq
    exact mul_left_cancel hEq
  have hmod := pow_eq_pow_iff_modEq.1 hx
  rw [h.orderOf_x] at hmod
  have : c = c' := ZMod.val_injective _ (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt c)
    (ZMod.val_lt c'))
  rw [this]

@[expose] def nfEquiv : ZMod 3 × (Fin 4 → ZMod 3) ≃ threeQ x v :=
  Equiv.ofBijective (fun p => ⟨threeNF x v p.1 p.2, nf_mem p.1 p.2⟩)
    ⟨fun p q e => h.nf_injective (congrArg Subtype.val e), fun g => by
      obtain ⟨c, e, he⟩ := h.mem_range_nf g.2
      exact ⟨(c, e), Subtype.ext he.symm⟩⟩

theorem nfEquiv_apply (p : ZMod 3 × (Fin 4 → ZMod 3)) :
    (h.nfEquiv p : G) = threeNF x v p.1 p.2 := rfl

theorem card_threeQ : Nat.card (threeQ x v) = 243 := by
  rw [← Nat.card_congr h.nfEquiv, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

theorem zpowers_pow_three {z : G} (hz : z ∈ zpowers x) : z ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := hz
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.xcube, one_zpow]

theorem pow_three_of_mem {g : G} (hg : g ∈ threeQ x v) : g ^ 3 = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact h.gen_pow_three' hs
  | one => exact one_pow 3
  | mul a b ha hb iha ihb =>
    rw [mul_pow_of_commute (h.comm_comm hb ha ha) (h.comm_comm hb ha hb), iha, ihb, one_mul,
      one_mul, show Nat.choose 3 2 = 3 * 1 by decide, pow_mul, h.zpowers_pow_three
        (h.comm_mem hb ha), one_pow]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem exponent_threeQ : Monoid.exponent (threeQ x v) = 3 := by
  have hdvd : Monoid.exponent (threeQ x v) ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (h.pow_three_of_mem g.2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdvd with he | he
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 he
    have : (⟨x, x_mem⟩ : threeQ x v) = 1 := Subsingleton.elim _ _
    exact h.x1 (congrArg Subtype.val this)
  · exact he

@[expose] def threeForm (ω : Fin 4 → Fin 4 → ZMod 3) (e : Fin 4 → ZMod 3) (j : Fin 4) : ZMod 3 :=
  ∑ i, e i * ω i j

theorem x_pow_eq_x_pow_val (n : ℕ) : x ^ n = x ^ ((n : ZMod 3).val) := by
  rw [ZMod.val_natCast, pow_mod_three h.xcube]

theorem comm_nf' (c : ZMod 3) (e : Fin 4 → ZMod 3) (j : Fin 4) :
    ⁅threeNF x v c e, v j⁆ = x ^ (threeForm ω e j).val := by
  rw [h.comm_nf, h.x_pow_eq_x_pow_val, threeForm, Fin.sum_univ_four]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  congr 2
  ring

theorem x_pow_val_inj {a b : ZMod 3} (hab : x ^ a.val = x ^ b.val) : a = b := by
  have hmod := pow_eq_pow_iff_modEq.1 hab
  rw [h.orderOf_x] at hmod
  exact ZMod.val_injective _ (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt a) (ZMod.val_lt b))

theorem threeForm_injective : Function.Injective (threeForm ω) := by
  intro e e' he
  have : e - e' = 0 := h.nondeg _ fun j => by
    have := congrFun he j
    simp only [threeForm] at this
    simp only [Pi.sub_apply, sub_mul]
    simp only [Fin.sum_univ_four] at this ⊢
    linear_combination this
  exact sub_eq_zero.1 this

omit [Group G] h in
theorem threeForm_add (e e' : Fin 4 → ZMod 3) :
    threeForm ω (e + e') = threeForm ω e + threeForm ω e' := by
  funext j
  simp only [threeForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[expose] def coord (g : threeQ x v) : Fin 4 → ZMod 3 := (h.nfEquiv.symm g).2

theorem coord_nf (c : ZMod 3) (e : Fin 4 → ZMod 3) : h.coord ⟨threeNF x v c e, nf_mem c e⟩ = e := by
  have : (⟨threeNF x v c e, nf_mem c e⟩ : threeQ x v) = h.nfEquiv (c, e) := rfl
  rw [coord, this, Equiv.symm_apply_apply]

theorem eq_nf (g : threeQ x v) : (g : G) = threeNF x v (h.nfEquiv.symm g).1 (h.coord g) := by
  conv_lhs => rw [← h.nfEquiv.apply_symm_apply g]
  rfl

theorem comm_coord (g : threeQ x v) (j : Fin 4) :
    ⁅(g : G), v j⁆ = x ^ (threeForm ω (h.coord g) j).val := by
  rw [h.eq_nf g, h.comm_nf']

theorem coord_mul (g g' : threeQ x v) : h.coord (g * g') = h.coord g + h.coord g' := by
  apply h.threeForm_injective
  funext j
  apply h.x_pow_val_inj
  have e := h.comm_coord (g * g') j
  rw [Subgroup.coe_mul, commutator_mul_left_of_commute (h.comm_comm g'.2 (v_mem j) g.2),
    h.comm_coord, h.comm_coord, ← pow_add] at e
  rw [← e, threeForm_add, Pi.add_apply, ZMod.val_add, pow_mod_three h.xcube, Nat.add_comm]

@[expose] def coordHom : threeQ x v →* Multiplicative (Fin 4 → ZMod 3) where
  toFun g := Multiplicative.ofAdd (h.coord g)
  map_one' := by
    have : (1 : threeQ x v) = ⟨threeNF x v 0 0, nf_mem 0 0⟩ := Subtype.ext nf_zero.symm
    rw [this, h.coord_nf]; rfl
  map_mul' g g' := by rw [h.coord_mul]; rfl

theorem coord_eq_zero_iff (g : threeQ x v) : h.coord g = 0 ↔ (g : G) ∈ zpowers x := by
  constructor
  · intro hg
    rw [h.eq_nf g, hg, threeNF]
    simp only [Pi.zero_apply, ZMod.val_zero, pow_zero, one_mul]
    exact npow_mem_zpowers x _
  · intro hg
    apply h.threeForm_injective
    funext j
    apply h.x_pow_val_inj
    rw [← h.comm_coord, commutatorElement_eq_one_iff_mul_comm.2
      ((h.zpowers_comm hg (v_mem j)).eq)]
    simp [threeForm]

theorem coordHom_ker : h.coordHom.ker = (zpowers x).subgroupOf (threeQ x v) := by
  ext g
  rw [MonoidHom.mem_ker, mem_subgroupOf, ← h.coord_eq_zero_iff]
  exact Multiplicative.ofAdd.injective.eq_iff' rfl

theorem coordHom_surjective : Function.Surjective h.coordHom := fun e =>
  ⟨⟨threeNF x v 0 (Multiplicative.toAdd e), nf_mem _ _⟩, by
    change Multiplicative.ofAdd _ = e
    rw [h.coord_nf]; rfl⟩

theorem zpowers_normal : ((zpowers x).subgroupOf (threeQ x v)).Normal := by
  rw [← h.coordHom_ker]; infer_instance

@[expose] def quotEquiv [((zpowers x).subgroupOf (threeQ x v)).Normal] :
    threeQ x v ⧸ (zpowers x).subgroupOf (threeQ x v) ≃* Multiplicative (Fin 4 → ZMod 3) :=
  (QuotientGroup.quotientMulEquivOfEq h.coordHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ h.coordHom_surjective)

theorem quotEquiv_mk [((zpowers x).subgroupOf (threeQ x v)).Normal] (g : threeQ x v) :
    h.quotEquiv (g : threeQ x v ⧸ (zpowers x).subgroupOf (threeQ x v)) =
      Multiplicative.ofAdd (h.coord g) := rfl

theorem mem_center_iff (g : threeQ x v) : g ∈ center (threeQ x v) ↔ (g : G) ∈ zpowers x := by
  constructor
  · intro hg
    rw [← h.coord_eq_zero_iff]
    apply h.threeForm_injective
    funext j
    apply h.x_pow_val_inj
    rw [← h.comm_coord]
    have := (Subgroup.mem_center_iff.1 hg) ⟨v j, v_mem j⟩
    rw [commutatorElement_eq_one_iff_mul_comm.2 (congrArg Subtype.val this).symm]
    simp [threeForm]
  · intro hg
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (h.zpowers_comm hg k.2).symm.eq

theorem center_map : (center (threeQ x v)).map (threeQ x v).subtype = zpowers x := by
  ext g
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (h.mem_center_iff q).1 hq
  · intro hg
    have hgQ : g ∈ threeQ x v := (zpowers_le.2 x_mem) hg
    exact ⟨⟨g, hgQ⟩, (h.mem_center_iff ⟨g, hgQ⟩).2 hg, rfl⟩

theorem card_center : Nat.card (center (threeQ x v)) = 3 := by
  rw [← card_map_of_injective (threeQ x v).subtype_injective, h.center_map, Nat.card_zpowers,
    h.orderOf_x]

theorem exists_comm_ne_one : ∃ i j, ⁅v i, v j⁆ ≠ 1 := by
  by_contra hall
  push Not at hall
  have : (Pi.single 0 1 : Fin 4 → ZMod 3) = 0 := h.nondeg _ fun j => by
    have hj := hall 0 j
    rw [h.comm] at hj
    have h0 : ω 0 j = 0 := by
      rw [h.x_pow_eq_one_iff, ZMod.natCast_val, ZMod.cast_id', id] at hj
      exact hj
    rw [Fin.sum_univ_four]
    simp [h0]
  have := congrFun this 0
  simp only [Pi.single_eq_same, Pi.zero_apply] at this
  exact absurd this (by decide)

theorem commutator_eq_center : commutator (threeQ x v) = center (threeQ x v) := by
  have hle : commutator (threeQ x v) ≤ center (threeQ x v) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g _ k _
    rw [h.mem_center_iff]
    exact h.comm_mem g.2 k.2
  have : Fact (Nat.card (center (threeQ x v))).Prime := ⟨by rw [h.card_center]; norm_num⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card
    ((commutator (threeQ x v)).subgroupOf (center (threeQ x v))) with hb | ht
  · exfalso
    obtain ⟨i, j, hij⟩ := h.exists_comm_ne_one
    have hmem : ⁅(⟨v i, v_mem i⟩ : threeQ x v), ⟨v j, v_mem j⟩⁆ ∈ commutator (threeQ x v) := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
    have hc : ⁅(⟨v i, v_mem i⟩ : threeQ x v), ⟨v j, v_mem j⟩⁆ ∈ center (threeQ x v) := hle hmem
    have : (⟨_, hc⟩ : center (threeQ x v)) ∈ (commutator (threeQ x v)).subgroupOf
        (center (threeQ x v)) := hmem
    rw [hb, mem_bot] at this
    apply hij
    have h2 := congrArg (fun z : center (threeQ x v) => ((z : threeQ x v) : G)) this
    simp only [Subgroup.coe_one, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [commutatorElement_def]
    exact h2
  · apply le_antisymm hle
    intro g hg
    have : (⟨g, hg⟩ : center (threeQ x v)) ∈ (commutator (threeQ x v)).subgroupOf
        (center (threeQ x v)) := by rw [ht]; trivial
    exact this


@[expose] def threePair (ω : Fin 4 → Fin 4 → ZMod 3) (e e' : Fin 4 → ZMod 3) : ZMod 3 :=
  ∑ j, threeForm ω e j * e' j

theorem comm_g_nf (g : threeQ x v) (c : ZMod 3) (e : Fin 4 → ZMod 3) :
    ⁅(g : G), threeNF x v c e⁆ = x ^ (threePair ω (h.coord g) e).val := by
  have hv : ∀ i, v i ∈ threeQ x v := fun i => v_mem i
  have hm : ∀ {s : G}, s ∈ threeQ x v → ∀ k ∈ threeQ x v, Commute ⁅(g : G), s⁆ k :=
    fun hs k hk => h.comm_comm g.2 hs hk
  have h3 := pow_mem (hv 3) (e 3).val
  have h2 := pow_mem (hv 2) (e 2).val
  have h1 := pow_mem (hv 1) (e 1).val
  have h0 := pow_mem (hv 0) (e 0).val
  have hx := pow_mem (x_mem (x := x) (v := v)) c.val
  have hpow : ∀ j (n : ℕ), ⁅(g : G), v j ^ n⁆ = x ^ ((threeForm ω (h.coord g) j).val * n) := by
    intro j n
    rw [commutator_pow_right_of_commute (h.comm_comm g.2 (hv j) (hv j)), h.comm_coord, pow_mul]
  have hxc : ⁅(g : G), x ^ c.val⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ((h.x_comm g.2).pow_left c.val).eq.symm
  unfold threeNF
  rw [commutator_mul_right_of_commute (hm hx _ (mul_mem (mul_mem (mul_mem h3 h2) h1) h0)), hxc,
    mul_one, commutator_mul_right_of_commute (hm h0 _ (mul_mem (mul_mem h3 h2) h1)),
    commutator_mul_right_of_commute (hm h1 _ (mul_mem h3 h2)),
    commutator_mul_right_of_commute (hm h2 _ h3), hpow, hpow, hpow, hpow, ← pow_add, ← pow_add,
    ← pow_add, h.x_pow_eq_x_pow_val, threePair, Fin.sum_univ_four]
  congr 2
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  ring

theorem comm_coord_coord (g k : threeQ x v) :
    ⁅(g : G), (k : G)⁆ = x ^ (threePair ω (h.coord g) (h.coord k)).val := by
  rw [h.eq_nf k, h.comm_g_nf]

theorem commute_iff (g k : threeQ x v) :
    g * k = k * g ↔ threePair ω (h.coord g) (h.coord k) = 0 := by
  have e : threePair ω (h.coord g) (h.coord k) = 0 ↔
      x ^ (threePair ω (h.coord g) (h.coord k)).val = 1 := by
    rw [h.x_pow_eq_one_iff, ZMod.natCast_val, ZMod.cast_id', id]
  rw [e, ← h.comm_coord_coord, commutatorElement_eq_one_iff_mul_comm, Subtype.ext_iff,
    Subgroup.coe_mul, Subgroup.coe_mul]

theorem threeForm_ne_zero {u : Fin 4 → ZMod 3} (hu : u ≠ 0) : threeForm ω u ≠ 0 := by
  intro h0
  apply hu
  apply h.threeForm_injective
  rw [h0]
  funext j
  simp [threeForm]

theorem card_centralizer (g : threeQ x v) (hg : (g : G) ∉ zpowers x) :
    Nat.card (centralizer {g} : Subgroup (threeQ x v)) = 81 := by
  have hu : h.coord g ≠ 0 := fun h0 => hg ((h.coord_eq_zero_iff g).1 h0)
  have e : (centralizer {g} : Subgroup (threeQ x v)) ≃
      {p : ZMod 3 × (Fin 4 → ZMod 3) // threePair ω (h.coord g) p.2 = 0} :=
    { toFun := fun k => ⟨h.nfEquiv.symm k, by
        have hk := mem_centralizer_singleton_iff.1 k.2
        exact (h.commute_iff g k).1 hk.symm⟩
      invFun := fun p => ⟨h.nfEquiv p.1, by
        rw [mem_centralizer_singleton_iff]
        refine ((h.commute_iff g _).2 ?_).symm
        have hc : h.coord (h.nfEquiv p.1) = p.1.2 := by
          unfold ThreeQRel.coord
          rw [Equiv.symm_apply_apply]
        rw [hc]
        exact p.2⟩
      left_inv := fun k => Subtype.ext (by simp)
      right_inv := fun p => Subtype.ext (by simp) }
  have e2 : {p : ZMod 3 × (Fin 4 → ZMod 3) // threePair ω (h.coord g) p.2 = 0} ≃
      ZMod 3 × {u : Fin 4 → ZMod 3 // ∑ j, threeForm ω (h.coord g) j * u j = 0} :=
    { toFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
      invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr (e.trans e2), Nat.card_prod, Nat.card_eq_fintype_card (α := ZMod 3),
    ZMod.card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    card_kernel _ (h.threeForm_ne_zero hu)]

theorem finite : Finite (threeQ x v) := Finite.of_equiv _ h.nfEquiv

theorem card_threeQ_type : Nat.card (threeQ x v) = 243 := h.card_threeQ

theorem not_commutative : ¬ ∀ a b : threeQ x v, a * b = b * a := by
  intro hall
  obtain ⟨i, j, hij⟩ := h.exists_comm_ne_one
  apply hij
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact congrArg Subtype.val (hall ⟨v i, v_mem i⟩ ⟨v j, v_mem j⟩)

omit [Group G] h in
theorem pow_of_dvd {n : ℕ} (hn : n ∣ 243) : n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 ∨ n = 81 ∨ n = 243 := by
  have h243 : (243 : ℕ) = 3 ^ 5 := by norm_num
  rw [h243, Nat.dvd_prime_pow Nat.prime_three] at hn
  obtain ⟨k, hk, rfl⟩ := hn
  interval_cases k <;> simp

theorem card_dvd (B : Subgroup (threeQ x v)) : Nat.card B ∣ 243 := by
  have := h.finite
  rw [← h.card_threeQ_type]
  exact Subgroup.card_subgroup_dvd_card B

theorem mem_center_of_val {g : threeQ x v} (hg : (g : G) ∈ zpowers x) : g ∈ center (threeQ x v) :=
  (h.mem_center_iff g).2 hg

theorem not_abelian_81 (B : Subgroup (threeQ x v)) (hZ : center (threeQ x v) ≤ B)
    (h81 : Nat.card B = 81) : ¬ ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
  have := h.finite
  intro hab
  have hZ3 := h.card_center
  have hC : ∀ b ∈ B, b ∉ center (threeQ x v) → (centralizer {b} : Subgroup _) = B := by
    intro b hb hbz
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · intro a ha
      rw [mem_centralizer_singleton_iff]
      exact (hab b hb a ha).symm
    · rw [h81, h.card_centralizer b fun hx => hbz (h.mem_center_of_val hx)]
  obtain ⟨k, hk⟩ : ∃ k : threeQ x v, k ∉ B := by
    by_contra hall
    push Not at hall
    have : B = ⊤ := eq_top_iff.2 fun k _ => hall k
    have hc := Nat.card_congr (Subgroup.topEquiv (G := threeQ x v)).toEquiv
    rw [← this, h81, h.card_threeQ_type] at hc
    norm_num at hc
  have hkz : k ∉ center (threeQ x v) := fun hz => hk (hZ hz)
  have hCk := h.card_centralizer k fun hx => hkz (h.mem_center_of_val hx)
  have hidx : ((centralizer {k} : Subgroup _) ⊓ B).index ≤ 9 := by
    have i1 : (centralizer {k} : Subgroup (threeQ x v)).index = 3 := by
      have := (centralizer {k} : Subgroup (threeQ x v)).card_mul_index
      rw [hCk, h.card_threeQ_type] at this
      omega
    have i2 : B.index = 3 := by
      have := B.card_mul_index
      rw [h81, h.card_threeQ_type] at this
      omega
    have := Subgroup.index_inf_le (H := (centralizer {k} : Subgroup (threeQ x v))) (K := B)
    rw [i1, i2] at this
    exact this
  have hcard : 27 ≤ Nat.card ((centralizer {k} : Subgroup (threeQ x v)) ⊓ B :
      Subgroup _) := by
    have := ((centralizer {k} : Subgroup (threeQ x v)) ⊓ B).card_mul_index
    rw [h.card_threeQ_type] at this
    have hpos : 0 < ((centralizer {k} : Subgroup (threeQ x v)) ⊓ B).index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    nlinarith
  obtain ⟨b, hb, hbz⟩ : ∃ b ∈ (centralizer {k} : Subgroup (threeQ x v)) ⊓ B,
      b ∉ center (threeQ x v) := by
    by_contra hall
    push Not at hall
    have hle : ((centralizer {k} : Subgroup (threeQ x v)) ⊓ B) ≤ center (threeQ x v) :=
      fun b hb => hall b hb
    have := Subgroup.card_le_of_le hle
    rw [hZ3] at this
    omega
  have hkb : k ∈ (centralizer {b} : Subgroup (threeQ x v)) := by
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hb).1).symm
  rw [hC b (Subgroup.mem_inf.1 hb).2 hbz] at hkb
  exact hk hkb

omit h in
theorem sup_center_abelian (B : Subgroup (threeQ x v)) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ∀ a ∈ B ⊔ center (threeQ x v), ∀ b ∈ B ⊔ center (threeQ x v), a * b = b * a := by
  intro a ha b hb
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ha
  obtain ⟨y', hy', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hb
  have c1 := Subgroup.mem_center_iff.1 hz
  have c2 := Subgroup.mem_center_iff.1 hz'
  calc y * z * (y' * z') = y * (z * y') * z' := by group
    _ = y * (y' * z) * z' := by rw [← c1 y']
    _ = y * y' * (z * z') := by group
    _ = y' * y * (z' * z) := by rw [hab y hy y' hy', c2 z]
    _ = y' * (y * z') * z := by group
    _ = y' * (z' * y) * z := by rw [c2 y]
    _ = y' * z' * (y * z) := by group

theorem card_sup_center_ge (B : Subgroup (threeQ x v)) :
    Nat.card B ≤ Nat.card (B ⊔ center (threeQ x v) : Subgroup _) := by
  have := h.finite
  exact Subgroup.card_le_of_le le_sup_left

theorem card_le_of_abelian (B : Subgroup (threeQ x v)) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ 27 := by
  have := h.finite
  by_contra hlt
  push Not at hlt
  have hB' := sup_center_abelian B hab
  have hge := h.card_sup_center_ge B
  have hd := h.card_dvd (B ⊔ center (threeQ x v))
  rcases ThreeQRel.pow_of_dvd hd with h1 | h1 | h1 | h1 | h1 | h1 <;>
    try omega
  · exact h.not_abelian_81 _ le_sup_right h1 hB'
  · apply h.not_commutative
    have htop : B ⊔ center (threeQ x v) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h1, h.card_threeQ_type])
    intro a b
    exact hB' a (by rw [htop]; trivial) b (by rw [htop]; trivial)

theorem center_le_of_abelian (B : Subgroup (threeQ x v)) (hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (h27 : Nat.card B = 27) : center (threeQ x v) ≤ B := by
  have := h.finite
  by_contra hnot
  have hB' := sup_center_abelian B hab
  have hlt : B < B ⊔ center (threeQ x v) :=
    lt_of_le_of_ne le_sup_left fun he => hnot (he ▸ le_sup_right)
  have hcard : 27 < Nat.card (B ⊔ center (threeQ x v) : Subgroup _) := by
    rw [← h27]
    exact Subgroup.card_lt_of_lt hlt
  have hd := h.card_dvd (B ⊔ center (threeQ x v))
  rcases ThreeQRel.pow_of_dvd hd with h1 | h1 | h1 | h1 | h1 | h1 <;>
    try omega
  · exact h.not_abelian_81 _ le_sup_right h1 hB'
  · apply h.not_commutative
    have htop : B ⊔ center (threeQ x v) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h1, h.card_threeQ_type])
    intro a b
    exact hB' a (by rw [htop]; trivial) b (by rw [htop]; trivial)

theorem isPGroup : IsPGroup 3 (threeQ x v) :=
  IsPGroup.of_card (n := 5) (by rw [h.card_threeQ_type]; norm_num)

theorem isExtraspecial : CFSG.IsExtraspecialPGroup 3 (threeQ x v) := by
  have := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hexp : ∀ g : threeQ x v, g ^ 3 = 1 := fun g => Subtype.ext (h.pow_three_of_mem g.2)
  refine ⟨h.isPGroup, h.commutator_eq_center, ?_, h.card_center⟩
  rw [CFSG.RankThree.PartTwo.frattini_eq_commutator h.isPGroup hexp, h.commutator_eq_center]

end ThreeQRel

end CFSG.RankThree.Native.ONTriple
