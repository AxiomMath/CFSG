module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

theorem apply_eq_self_of_commute_isThreeCycle {α : Type*} [Fintype α] [DecidableEq α]
    {c y : Perm α} (hc : c.IsThreeCycle) (hyc : Commute y c) (hy : Nat.Coprime (orderOf y) 3)
    {a : α} (ha : c a ≠ a) : y a = a := by
  have hcy : c (y a) ≠ y a := by
    intro h
    apply ha
    apply y.injective
    rw [← Perm.mul_apply, hyc.eq, Perm.mul_apply, h]
  obtain ⟨i, -, hi⟩ := (hc.isCycle.sameCycle ha hcy).exists_pow_eq'
  have key : ∀ m : ℕ, (y ^ m) a = (c ^ (i * m)) a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Perm.mul_apply, ih, ← Perm.mul_apply, ((hyc.pow_right (i * m)).eq),
        Perm.mul_apply, ← hi, ← Perm.mul_apply, ← pow_add, Nat.mul_succ]
  have h1 : (c ^ (i * orderOf y)) a = a := by
    rw [← key, pow_orderOf_eq_one, Perm.one_apply]
  have h2 : c ^ (i * orderOf y) = 1 := (hc.isCycle.pow_eq_one_iff' ha).mpr h1
  have h3 : 3 ∣ i * orderOf y := by
    rw [← hc.orderOf]
    exact orderOf_dvd_of_pow_eq_one h2
  have h4 : 3 ∣ i := (Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_comm.mp hy) h3)
  have h5 : c ^ i = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hc.orderOf]
    exact h4
  rw [← hi, h5, Perm.one_apply]

theorem factorization_three_pow_mul (k : ℕ) {m : ℕ} (hm : ¬ 3 ∣ m) :
    (3 ^ k * m).factorization 3 = k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (pow_ne_zero k (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

section Vectors

variable {k : ℕ} {H : Type*} [Group H]

theorem card_range_of_injective (φ : Multiplicative (Fin k → ZMod 3) →* H)
    (hφ : Function.Injective φ) : Nat.card φ.range = 3 ^ k := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem isElemAbelian_range (φ : Multiplicative (Fin k → ZMod 3) →* H) :
    IsMulCommutative φ.range ∧ ∀ x ∈ φ.range, x ^ 3 = 1 := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨u, rfl⟩⟩ := a
    obtain ⟨_, ⟨v, rfl⟩⟩ := b
    change φ u * φ v = φ v * φ u
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨u, rfl⟩
    rw [← map_pow]
    have : u ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      ext i
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    rw [this, map_one]

end Vectors

section Std

variable (n : ℕ) [NeZero n]

@[expose] def c1 : Perm (Fin n) := swap 0 1 * swap 1 2

@[expose] def c2 : Perm (Fin n) := swap 3 4 * swap 4 5

@[expose] def c3 : Perm (Fin n) := swap 6 7 * swap 7 8

@[expose] def tt : Perm (Fin n) :=
  swap 0 3 * swap 3 6 * (swap 1 4 * swap 4 7) * (swap 2 5 * swap 5 8)

@[expose] def dd : Perm (Fin n) := swap 9 10 * swap 10 11

@[expose] def vecPerm2 (v : Fin 2 → ZMod 3) : Perm (Fin n) :=
  c1 n ^ (v 0).val * c2 n ^ (v 1).val

@[expose] def vecPerm (v : Fin 3 → ZMod 3) : Perm (Fin n) :=
  c1 n ^ (v 0).val * c2 n ^ (v 1).val * c3 n ^ (v 2).val

@[expose] def F0 : Subgroup (Perm (Fin n)) := zpowers (c1 n) ⊔ zpowers (c2 n)

@[expose] def A0 : Subgroup (Perm (Fin n)) := F0 n ⊔ zpowers (c3 n)

@[expose] def W : Subgroup (Perm (Fin n)) := A0 n ⊔ zpowers (tt n)

@[expose] def W12 : Subgroup (Perm (Fin n)) := W n ⊔ zpowers (dd n)

end Std

section F0

variable {n : ℕ} [NeZero n]

structure F0Facts (n : ℕ) [NeZero n] : Prop where
  add : ∀ v w : Fin 2 → ZMod 3, vecPerm2 n (v + w) = vecPerm2 n v * vecPerm2 n w
  inj : ∀ v : Fin 2 → ZMod 3, vecPerm2 n v = 1 → v = 0
  e1 : vecPerm2 n ![1, 0] = c1 n
  e2 : vecPerm2 n ![0, 1] = c2 n

@[expose] def vecHom2 (hf : F0Facts n) : Multiplicative (Fin 2 → ZMod 3) →* Perm (Fin n) where
  toFun v := vecPerm2 n (Multiplicative.toAdd v)
  map_one' := by simp [vecPerm2]
  map_mul' u v := hf.add _ _

theorem vecHom2_injective (hf : F0Facts n) : Function.Injective (vecHom2 hf) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  exact Multiplicative.toAdd.injective (hf.inj _ hv)

theorem F0_eq_range (hf : F0Facts n) : F0 n = (vecHom2 hf).range := by
  apply le_antisymm
  · refine sup_le (zpowers_le.mpr ⟨Multiplicative.ofAdd ![1, 0], hf.e1⟩)
      (zpowers_le.mpr ⟨Multiplicative.ofAdd ![0, 1], hf.e2⟩)
  · rintro _ ⟨v, rfl⟩
    exact mul_mem (pow_mem (mem_sup_left (mem_zpowers _)) _)
      (pow_mem (mem_sup_right (mem_zpowers _)) _)

theorem card_F0 (hf : F0Facts n) : Nat.card (F0 n) = 9 := by
  rw [F0_eq_range hf, card_range_of_injective _ (vecHom2_injective hf)]
  norm_num

theorem isElemAbelian_F0 (hf : F0Facts n) :
    IsMulCommutative (F0 n) ∧ ∀ x ∈ F0 n, x ^ 3 = 1 := by
  rw [F0_eq_range hf]
  exact isElemAbelian_range _

theorem isPGroup_F0 (hf : F0Facts n) : IsPGroup 3 (F0 n) :=
  IsPGroup.of_card (n := 2) (by rw [card_F0 hf]; norm_num)

end F0

section A0

variable {n : ℕ} [NeZero n]

structure A0Facts (n : ℕ) [NeZero n] : Prop where
  add : ∀ v w : Fin 3 → ZMod 3, vecPerm n (v + w) = vecPerm n v * vecPerm n w
  inj : ∀ v : Fin 3 → ZMod 3, vecPerm n v = 1 → v = 0
  e1 : vecPerm n ![1, 0, 0] = c1 n
  e2 : vecPerm n ![0, 1, 0] = c2 n
  e3 : vecPerm n ![0, 0, 1] = c3 n

@[expose] def vecHom (hf : A0Facts n) : Multiplicative (Fin 3 → ZMod 3) →* Perm (Fin n) where
  toFun v := vecPerm n (Multiplicative.toAdd v)
  map_one' := by simp [vecPerm]
  map_mul' u v := hf.add _ _

theorem vecHom_apply (hf : A0Facts n) (v : Multiplicative (Fin 3 → ZMod 3)) :
    vecHom hf v = vecPerm n (Multiplicative.toAdd v) :=
  rfl

theorem vecHom_injective (hf : A0Facts n) : Function.Injective (vecHom hf) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  exact Multiplicative.toAdd.injective (hf.inj _ hv)

theorem A0_eq_range (hf : A0Facts n) : A0 n = (vecHom hf).range := by
  apply le_antisymm
  · refine sup_le (sup_le (zpowers_le.mpr ⟨Multiplicative.ofAdd ![1, 0, 0], hf.e1⟩)
      (zpowers_le.mpr ⟨Multiplicative.ofAdd ![0, 1, 0], hf.e2⟩))
      (zpowers_le.mpr ⟨Multiplicative.ofAdd ![0, 0, 1], hf.e3⟩)
  · rintro _ ⟨v, rfl⟩
    exact mul_mem (mul_mem (pow_mem (mem_sup_left (mem_sup_left (mem_zpowers _))) _)
      (pow_mem (mem_sup_left (mem_sup_right (mem_zpowers _))) _))
      (pow_mem (mem_sup_right (mem_zpowers _)) _)

theorem mem_A0 (hf : A0Facts n) {x : Perm (Fin n)} : x ∈ A0 n ↔ ∃ v, vecPerm n v = x := by
  rw [A0_eq_range hf]
  exact ⟨fun ⟨v, hv⟩ => ⟨_, hv⟩, fun ⟨v, hv⟩ => ⟨Multiplicative.ofAdd v, hv⟩⟩

theorem vecPerm_mem_A0 (hf : A0Facts n) (v : Fin 3 → ZMod 3) : vecPerm n v ∈ A0 n :=
  (mem_A0 hf).mpr ⟨v, rfl⟩

theorem card_A0 (hf : A0Facts n) : Nat.card (A0 n) = 27 := by
  rw [A0_eq_range hf, card_range_of_injective _ (vecHom_injective hf)]
  norm_num

theorem isElemAbelian_A0 (hf : A0Facts n) :
    IsMulCommutative (A0 n) ∧ ∀ x ∈ A0 n, x ^ 3 = 1 := by
  rw [A0_eq_range hf]
  exact isElemAbelian_range _

theorem isPGroup_A0 (hf : A0Facts n) : IsPGroup 3 (A0 n) :=
  IsPGroup.of_card (n := 3) (by rw [card_A0 hf]; norm_num)

theorem commute_of_mem_A0 (hf : A0Facts n) {x y : Perm (Fin n)} (hx : x ∈ A0 n)
    (hy : y ∈ A0 n) : x * y = y * x :=
  congrArg Subtype.val ((isElemAbelian_A0 hf).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem vecPerm_mem_zpowers_of_const (hf : A0Facts n) {u : Fin 3 → ZMod 3} (h01 : u 0 = u 1)
    (h12 : u 1 = u 2) : vecPerm n u ∈ zpowers (vecPerm n ![1, 1, 1]) := by
  have hu : Multiplicative.ofAdd u = (Multiplicative.ofAdd ![1, 1, 1]) ^ (u 0).val := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp [h01, h12]
  have h := congrArg (vecHom hf) hu
  rw [map_pow] at h
  change vecPerm n u = vecPerm n ![1, 1, 1] ^ (u 0).val at h
  rw [h]
  exact pow_mem (mem_zpowers _) _

end A0

section W

variable {n : ℕ} [NeZero n]

structure WFacts (n : ℕ) [NeZero n] : Prop extends A0Facts n where
  tt_pow : tt n ^ 3 = 1
  conj1 : tt n * c1 n * (tt n)⁻¹ = c2 n
  conj2 : tt n * c2 n * (tt n)⁻¹ = c3 n
  conj3 : tt n * c3 n * (tt n)⁻¹ = c1 n
  tt_ne : ∀ v : Fin 3 → ZMod 3, vecPerm n v ≠ tt n
  cent : ∀ (v : Fin 3 → ZMod 3) (j : Fin 3), j ≠ 0 →
    vecPerm n v * tt n ^ (j : ℕ) = tt n ^ (j : ℕ) * vecPerm n v → v 0 = v 1 ∧ v 1 = v 2

theorem conj_tt_mem_A0 (hf : WFacts n) {x : Perm (Fin n)} (hx : x ∈ A0 n) :
    tt n * x * (tt n)⁻¹ ∈ A0 n := by
  have hle : A0 n ≤ (A0 n).comap (MulAut.conj (tt n)).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [zpowers_le, mem_comap] <;>
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · rw [hf.conj1]
      exact mem_sup_left (mem_sup_right (mem_zpowers _))
    · rw [hf.conj2]
      exact mem_sup_right (mem_zpowers _)
    · rw [hf.conj3]
      exact mem_sup_left (mem_sup_left (mem_zpowers _))
  exact hle hx

theorem tt_mem_normalizer (hf : WFacts n) : tt n ∈ normalizer (A0 n : Set (Perm (Fin n))) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_tt_mem_A0 hf, fun hx => ?_⟩
  have h2 := conj_tt_mem_A0 hf (conj_tt_mem_A0 hf hx)
  have htt3 : tt n * tt n * tt n = 1 := by rw [← pow_three', hf.tt_pow]
  have h3 : tt n * (tt n * (tt n * x * (tt n)⁻¹) * (tt n)⁻¹) * (tt n)⁻¹ = x := by
    calc tt n * (tt n * (tt n * x * (tt n)⁻¹) * (tt n)⁻¹) * (tt n)⁻¹ =
        (tt n * tt n * tt n) * x * (tt n * tt n * tt n)⁻¹ := by group
      _ = x := by rw [htt3, one_mul, inv_one, mul_one]
  rw [← h3]
  exact h2

theorem zpowers_tt_le_normalizer (hf : WFacts n) :
    zpowers (tt n) ≤ normalizer (A0 n : Set (Perm (Fin n))) :=
  zpowers_le.mpr (tt_mem_normalizer hf)

theorem W_le_normalizer (hf : WFacts n) : W n ≤ normalizer (A0 n : Set (Perm (Fin n))) :=
  sup_le le_normalizer (zpowers_tt_le_normalizer hf)

theorem tt_ne_one (hf : WFacts n) : tt n ≠ 1 := by
  intro h
  apply hf.tt_ne 0
  rw [h]
  simp [vecPerm]

theorem orderOf_tt (hf : WFacts n) : orderOf (tt n) = 3 :=
  orderOf_eq_prime hf.tt_pow (tt_ne_one hf)

theorem isPGroup_zpowers_tt (hf : WFacts n) : IsPGroup 3 (zpowers (tt n)) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_tt hf, pow_one])

theorem isPGroup_W (hf : WFacts n) : IsPGroup 3 (W n) :=
  IsPGroup.to_sup_of_normal_left' (isPGroup_A0 hf.toA0Facts) (isPGroup_zpowers_tt hf)
    (zpowers_tt_le_normalizer hf)

theorem tt_mem_W : tt n ∈ W n := mem_sup_right (mem_zpowers _)

theorem tt_notMem_A0 (hf : WFacts n) : tt n ∉ A0 n := by
  rw [mem_A0 hf.toA0Facts]
  rintro ⟨v, hv⟩
  exact hf.tt_ne v hv

theorem mem_W (hf : WFacts n) {x : Perm (Fin n)} (hx : x ∈ W n) :
    ∃ (v : Fin 3 → ZMod 3) (j : Fin 3), x = vecPerm n v * tt n ^ (j : ℕ) := by
  classical
  have hx' : x ∈ ((A0 n : Set (Perm (Fin n))) * (zpowers (tt n) : Set (Perm (Fin n)))) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (zpowers_tt_le_normalizer hf)]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  obtain ⟨v, rfl⟩ := (mem_A0 hf.toA0Facts).mp ha
  rw [SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf, orderOf_tt hf, Finset.mem_image] at hb
  obtain ⟨j, hj, rfl⟩ := hb
  exact ⟨v, ⟨j, Finset.mem_range.mp hj⟩, rfl⟩

theorem le_card_W (hf : WFacts n) : 81 ≤ Nat.card (W n) := by
  obtain ⟨k, hk⟩ := (isPGroup_W hf).exists_card_eq
  have hle : A0 n ≤ W n := le_sup_left
  have hdvd : 3 ^ 3 ∣ 3 ^ k := by
    rw [← hk, show (3 : ℕ) ^ 3 = 27 by norm_num, ← card_A0 hf.toA0Facts]
    exact Subgroup.card_dvd_of_le hle
  have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hk4 : k ≠ 3 := by
    rintro rfl
    apply tt_notMem_A0 hf
    have heq : A0 n = W n :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hk, card_A0 hf.toA0Facts]; norm_num)
    rw [heq]
    exact tt_mem_W
  rw [hk]
  calc 81 = 3 ^ 4 := by norm_num
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem eq_A0_of_le_W (hf : WFacts n) (hW : Nat.card (W n) = 81) {E : Subgroup (Perm (Fin n))}
    (hEW : E ≤ W n) (hE : IsMulCommutative E ∧ ∀ x ∈ E, x ^ 3 = 1) (hE27 : Nat.card E = 27) :
    E = A0 n := by
  have hA := hf.toA0Facts
  by_contra hne
  have hnle : ¬ E ≤ A0 n := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hE27, card_A0 hA]))
  obtain ⟨x, hxE, hxA⟩ : ∃ x ∈ E, x ∉ A0 n := by
    by_contra hc
    push Not at hc
    exact hnle hc
  obtain ⟨v, j, rfl⟩ := mem_W hf (hEW hxE)
  have hj : j ≠ 0 := by
    rintro rfl
    apply hxA
    rw [Fin.val_zero, pow_zero, mul_one]
    exact vecPerm_mem_A0 hA v
  have hint : A0 n ⊓ E ≤ zpowers (vecPerm n ![1, 1, 1]) := by
    rintro b ⟨hbA, hbE⟩
    obtain ⟨u, rfl⟩ := (mem_A0 hA).mp hbA
    have hcomm : vecPerm n u * (vecPerm n v * tt n ^ (j : ℕ)) =
        vecPerm n v * tt n ^ (j : ℕ) * vecPerm n u :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hbE⟩ ⟨_, hxE⟩)
    have huv : vecPerm n u * vecPerm n v = vecPerm n v * vecPerm n u := by
      rw [← hA.add, ← hA.add, add_comm]
    have h2 : vecPerm n u * tt n ^ (j : ℕ) = tt n ^ (j : ℕ) * vecPerm n u := by
      have h3 : vecPerm n v * (vecPerm n u * tt n ^ (j : ℕ)) =
          vecPerm n v * (tt n ^ (j : ℕ) * vecPerm n u) := by
        rw [← mul_assoc, ← huv, mul_assoc, hcomm, mul_assoc]
      exact mul_left_cancel h3
    obtain ⟨h01, h12⟩ := hf.cent u j hj h2
    exact vecPerm_mem_zpowers_of_const hA h01 h12
  have hz3 : Nat.card (zpowers (vecPerm n ![1, 1, 1])) ≤ 3 := by
    rw [Nat.card_zpowers]
    apply Nat.le_of_dvd (by norm_num)
    exact orderOf_dvd_of_pow_eq_one ((isElemAbelian_A0 hA).2 _ (vecPerm_mem_A0 hA _))
  have hcardint : Nat.card (A0 n ⊓ E : Subgroup _) ≤ 3 :=
    (Subgroup.card_le_of_le hint).trans hz3
  have hrW : (A0 n).relIndex (W n) = 3 := by
    have hle : A0 n ≤ W n := le_sup_left
    have h := Subgroup.relIndex_mul_card (H := A0 n) (K := W n)
    rw [inf_of_le_left hle, card_A0 hA, hW] at h
    omega
  have hrE : (A0 n).relIndex E ≤ 3 := by
    rw [← hrW]
    exact Subgroup.relIndex_le_of_le_right hEW (by rw [hrW]; norm_num)
  have h := Subgroup.relIndex_mul_card (H := A0 n) (K := E)
  rw [hE27] at h
  have : (A0 n).relIndex E * Nat.card (A0 n ⊓ E : Subgroup _) ≤ 3 * 3 :=
    Nat.mul_le_mul hrE hcardint
  omega

end W

section Sylow

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem coe_smul_sylow_eq_map {p : ℕ} [Fact p.Prime] (g : G) (P : Sylow p G) :
    ((g • P : Sylow p G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, smul_inv_smul]
  · rintro ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, inv_smul_smul]
    exact hy

theorem card_eq_of_isPGroup_of_le {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p H)
    (hle : p ^ (Nat.card G).factorization p ≤ Nat.card H) :
    Nat.card H = p ^ (Nat.card G).factorization p := by
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  have h1 := Subgroup.card_le_of_le hP
  rw [Sylow.card_eq_multiplicity] at h1
  omega

theorem card_le_of_isPGroup {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p H) :
    Nat.card H ≤ p ^ (Nat.card G).factorization p := by
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  have h1 := Subgroup.card_le_of_le hP
  rwa [Sylow.card_eq_multiplicity] at h1

theorem exists_le_map_conj_of_card {p : ℕ} [Fact p.Prime] {P₀ E : Subgroup G}
    (hP₀ : Nat.card P₀ = p ^ (Nat.card G).factorization p) (hE : IsPGroup p E) :
    ∃ g : G, E ≤ P₀.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨P, hP⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (Sylow.ofCard P₀ hP₀) P
  refine ⟨g, ?_⟩
  have h := coe_smul_sylow_eq_map g (Sylow.ofCard P₀ hP₀)
  rw [hg] at h
  exact hP.trans_eq h

omit [Finite G] in
theorem map_conj_inv_le {P E : Subgroup G} {g : G} (h : E ≤ P.map (MulAut.conj g).toMonoidHom) :
    E.map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := h hx
  simpa [MulAut.conj_apply, mul_assoc] using hy

omit [Finite G] in
theorem map_conj_map_conj_inv (E : Subgroup G) (g : G) :
    (E.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = E := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id E
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end Sylow

theorem factorization_card_perm {n k m : ℕ} (h : n.factorial = 3 ^ k * m) (hm : ¬ 3 ∣ m) :
    (Nat.card (Perm (Fin n))).factorization 3 = k := by
  rw [Nat.card_perm, Nat.card_fin, h, factorization_three_pow_mul k hm]

theorem factorization_six : (Nat.card (Perm (Fin 6))).factorization 3 = 2 :=
  factorization_card_perm (m := 80) (by decide) (by decide)

theorem factorization_seven : (Nat.card (Perm (Fin 7))).factorization 3 = 2 :=
  factorization_card_perm (m := 560) (by decide) (by decide)

theorem factorization_eight : (Nat.card (Perm (Fin 8))).factorization 3 = 2 :=
  factorization_card_perm (m := 4480) (by decide) (by decide)

theorem factorization_nine : (Nat.card (Perm (Fin 9))).factorization 3 = 4 :=
  factorization_card_perm (m := 4480) (by decide) (by decide)

theorem factorization_ten : (Nat.card (Perm (Fin 10))).factorization 3 = 4 :=
  factorization_card_perm (m := 44800) (by decide) (by decide)

theorem factorization_eleven : (Nat.card (Perm (Fin 11))).factorization 3 = 4 :=
  factorization_card_perm (m := 492800) (by decide) (by decide)

theorem factorization_twelve : (Nat.card (Perm (Fin 12))).factorization 3 = 5 :=
  factorization_card_perm (m := 1971200) (by decide) (by decide)

section Conj

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem card_le_nine_of_isPGroup (h2 : (Nat.card (Perm (Fin n))).factorization 3 = 2)
    {E : Subgroup (Perm (Fin n))} (hE : IsPGroup 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := card_le_of_isPGroup hE
  rwa [h2] at h

theorem exists_eq_map_conj_F0 (hf : F0Facts n)
    (h2 : (Nat.card (Perm (Fin n))).factorization 3 = 2) {E : Subgroup (Perm (Fin n))}
    (hE : IsPGroup 3 E) (hE9 : Nat.card E = 9) :
    ∃ g : Perm (Fin n), E = (F0 n).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_le_map_conj_of_card (P₀ := F0 n)
    (by rw [card_F0 hf, h2]; norm_num) hE
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_F0 hf, hE9]

theorem exists_eq_map_conj_A0 (hf : WFacts n)
    (h4 : (Nat.card (Perm (Fin n))).factorization 3 = 4) {E : Subgroup (Perm (Fin n))}
    (hE : IsMulCommutative E ∧ ∀ x ∈ E, x ^ 3 = 1) (hE27 : Nat.card E = 27) :
    ∃ g : Perm (Fin n), E = (A0 n).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW : Nat.card (W n) = 81 := by
    have h := card_eq_of_isPGroup_of_le (isPGroup_W hf) (by rw [h4]; exact le_card_W hf)
    rw [h, h4]
    norm_num
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  obtain ⟨g, hg⟩ := exists_le_map_conj_of_card (P₀ := W n) (by rw [hW, h4]; norm_num) hEp
  refine ⟨g, ?_⟩
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hE'W : E' ≤ W n := map_conj_inv_le hg
  have hE'ab : IsMulCommutative E' ∧ ∀ x ∈ E', x ^ 3 = 1 := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      change (MulAut.conj g⁻¹).toMonoidHom x * (MulAut.conj g⁻¹).toMonoidHom y =
        (MulAut.conj g⁻¹).toMonoidHom y * (MulAut.conj g⁻¹).toMonoidHom x
      rw [← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  have hE'27 : Nat.card E' = 27 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hE27]
  have heq := eq_A0_of_le_W hf hW hE'W hE'ab hE'27
  rw [← heq, hE', map_conj_map_conj_inv]

end Conj

section W12

structure W12Facts : Prop where
  w : WFacts 12
  dd_pow : dd 12 ^ 3 = 1
  dd_c1 : dd 12 * c1 12 = c1 12 * dd 12
  dd_c2 : dd 12 * c2 12 = c2 12 * dd 12
  dd_c3 : dd 12 * c3 12 = c3 12 * dd 12
  dd_tt : dd 12 * tt 12 = tt 12 * dd 12
  fix9 : c1 12 9 = 9 ∧ c2 12 9 = 9 ∧ c3 12 9 = 9 ∧ tt 12 9 = 9
  dd9 : dd 12 9 ≠ 9
  z_tt : vecPerm 12 ![1, 1, 1] * tt 12 = tt 12 * vecPerm 12 ![1, 1, 1]

variable (hf : W12Facts)
include hf

theorem W_le_stabilizer_nine : W 12 ≤ MulAction.stabilizer (Perm (Fin 12)) (9 : Fin 12) := by
  obtain ⟨h1, h2, h3, h4⟩ := hf.fix9
  exact sup_le (sup_le (sup_le (zpowers_le.mpr h1) (zpowers_le.mpr h2)) (zpowers_le.mpr h3))
    (zpowers_le.mpr h4)

theorem dd_notMem_W : dd 12 ∉ W 12 := fun h => hf.dd9 (W_le_stabilizer_nine hf h)

theorem W_le_centralizer_dd : W 12 ≤ centralizer {dd 12} := by
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
  · exact hf.dd_c1.symm
  · exact hf.dd_c2.symm
  · exact hf.dd_c3.symm
  · exact hf.dd_tt.symm

theorem W12_le_centralizer_dd : W12 12 ≤ centralizer {dd 12} :=
  sup_le (W_le_centralizer_dd hf) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))

theorem W12_le_centralizer_z : W12 12 ≤ centralizer {vecPerm 12 ![1, 1, 1]} := by
  have hA := hf.w.toA0Facts
  have hzA : vecPerm 12 ![1, 1, 1] ∈ A0 12 := vecPerm_mem_A0 hA _
  have hA0 : A0 12 ≤ centralizer {vecPerm 12 ![1, 1, 1]} := fun x hx =>
    mem_centralizer_singleton_iff.mpr (commute_of_mem_A0 hA hx hzA)
  have hzW : vecPerm 12 ![1, 1, 1] ∈ W 12 := mem_sup_left hzA
  have hzd := mem_centralizer_singleton_iff.mp (W_le_centralizer_dd hf hzW)
  refine sup_le (sup_le hA0 (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hf.z_tt.symm)))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzd.symm))

theorem zpowers_dd_le_centralizer :
    zpowers (dd 12) ≤ centralizer (W 12 : Set (Perm (Fin 12))) := by
  rw [zpowers_le, mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.mp (W_le_centralizer_dd hf hx)

theorem dd_ne_one : dd 12 ≠ 1 := fun h => hf.dd9 (by rw [h, Perm.one_apply])

theorem isPGroup_zpowers_dd : IsPGroup 3 (zpowers (dd 12)) :=
  IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hf.dd_pow (dd_ne_one hf), pow_one])

theorem isPGroup_W12 : IsPGroup 3 (W12 12) :=
  IsPGroup.to_sup_of_normal_left' (isPGroup_W hf.w) (isPGroup_zpowers_dd hf)
    ((zpowers_dd_le_centralizer hf).trans (centralizer_le_normalizer _))

theorem card_W12 : Nat.card (W12 12) = 243 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : W 12 ≤ W12 12 := le_sup_left
  obtain ⟨k, hk⟩ := (isPGroup_W12 hf).exists_card_eq
  obtain ⟨j, hj⟩ := (isPGroup_W hf.w).exists_card_eq
  have h81 := le_card_W hf.w
  have hdvd : 3 ^ j ∣ 3 ^ k := by
    rw [← hj, ← hk]
    exact Subgroup.card_dvd_of_le hle
  have hjk : j ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hjk' : j ≠ k := by
    rintro rfl
    have heq : W 12 = W12 12 := Subgroup.eq_of_le_of_card_ge hle (by rw [hj, hk])
    exact dd_notMem_W hf (heq ▸ mem_sup_right (mem_zpowers _))
  have hj4 : 4 ≤ j := by
    by_contra hlt
    have : 3 ^ j ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hj] at h81
    omega
  have hub := card_le_of_isPGroup (isPGroup_W12 hf)
  rw [factorization_twelve, hk] at hub
  have hk5 : k ≤ 5 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hub
  have hk5' : k = 5 := by omega
  rw [hk, hk5']
  norm_num

theorem exists_le_map_conj_W12 {E : Subgroup (Perm (Fin 12))} (hE : IsPGroup 3 E) :
    ∃ g : Perm (Fin 12), E ≤ (W12 12).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_le_map_conj_of_card (by rw [card_W12 hf, factorization_twelve]; norm_num) hE

theorem commute_z_of_mem_map {g x : Perm (Fin 12)}
    (hx : x ∈ (W12 12).map (MulAut.conj g).toMonoidHom) :
    x * (g * vecPerm 12 ![1, 1, 1] * g⁻¹) = g * vecPerm 12 ![1, 1, 1] * g⁻¹ * x := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h := mem_centralizer_singleton_iff.mp (W12_le_centralizer_z hf hy)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * y * g⁻¹ * (g * vecPerm 12 ![1, 1, 1] * g⁻¹) = g * (y * vecPerm 12 ![1, 1, 1]) * g⁻¹ :=
        by group
    _ = g * (vecPerm 12 ![1, 1, 1] * y) * g⁻¹ := by rw [h]
    _ = g * vecPerm 12 ![1, 1, 1] * g⁻¹ * (g * y * g⁻¹) := by group

theorem commute_dd_of_mem_map {g x : Perm (Fin 12)}
    (hx : x ∈ (W12 12).map (MulAut.conj g).toMonoidHom) :
    x * (g * dd 12 * g⁻¹) = g * dd 12 * g⁻¹ * x := by
  obtain ⟨y, hy, rfl⟩ := hx
  have h := mem_centralizer_singleton_iff.mp (W12_le_centralizer_dd hf hy)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * y * g⁻¹ * (g * dd 12 * g⁻¹) = g * (y * dd 12) * g⁻¹ := by group
    _ = g * (dd 12 * y) * g⁻¹ := by rw [h]
    _ = g * dd 12 * g⁻¹ * (g * y * g⁻¹) := by group

end W12

theorem f0Facts_six : F0Facts 6 where
  add := by decide +kernel
  inj := by decide +kernel
  e1 := by decide +kernel
  e2 := by decide +kernel

theorem f0Facts_seven : F0Facts 7 where
  add := by decide +kernel
  inj := by decide +kernel
  e1 := by decide +kernel
  e2 := by decide +kernel

theorem f0Facts_eight : F0Facts 8 where
  add := by decide +kernel
  inj := by decide +kernel
  e1 := by decide +kernel
  e2 := by decide +kernel

theorem wFacts_nine : WFacts 9 where
  add := by decide +kernel
  inj := by decide +kernel
  e1 := by decide +kernel
  e2 := by decide +kernel
  e3 := by decide +kernel
  tt_pow := by decide +kernel
  conj1 := by decide +kernel
  conj2 := by decide +kernel
  conj3 := by decide +kernel
  tt_ne := by decide +kernel
  cent := by decide +kernel

theorem wFacts_ten : WFacts 10 where
  add := by decide +kernel
  inj := by decide +kernel
  e1 := by decide +kernel
  e2 := by decide +kernel
  e3 := by decide +kernel
  tt_pow := by decide +kernel
  conj1 := by decide +kernel
  conj2 := by decide +kernel
  conj3 := by decide +kernel
  tt_ne := by decide +kernel
  cent := by decide +kernel

theorem wFacts_eleven : WFacts 11 where
  add := by decide +kernel
  inj := by decide +kernel
  e1 := by decide +kernel
  e2 := by decide +kernel
  e3 := by decide +kernel
  tt_pow := by decide +kernel
  conj1 := by decide +kernel
  conj2 := by decide +kernel
  conj3 := by decide +kernel
  tt_ne := by decide +kernel
  cent := by decide +kernel

theorem wFacts_twelve : WFacts 12 where
  add := by decide +kernel
  inj := by decide +kernel
  e1 := by decide +kernel
  e2 := by decide +kernel
  e3 := by decide +kernel
  tt_pow := by decide +kernel
  conj1 := by decide +kernel
  conj2 := by decide +kernel
  conj3 := by decide +kernel
  tt_ne := by decide +kernel
  cent := by decide +kernel

theorem w12Facts : W12Facts where
  w := wFacts_twelve
  dd_pow := by decide +kernel
  dd_c1 := by decide +kernel
  dd_c2 := by decide +kernel
  dd_c3 := by decide +kernel
  dd_tt := by decide +kernel
  fix9 := by decide +kernel
  dd9 := by decide +kernel
  z_tt := by decide +kernel

end CFSG.RankThree.PartTwo.Sec4.Item434AltPerm
