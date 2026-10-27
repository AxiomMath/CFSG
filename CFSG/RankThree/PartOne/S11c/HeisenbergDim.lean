module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.RankThree.PartOne.HNRed

open Polynomial Module

section Algebra

variable {A : Type*} [Monoid A]

theorem pow_mod_five {T : A} (hT : T ^ 5 = 1) (a : ℕ) : T ^ a = T ^ (a % 5) := by
  conv_lhs => rw [← Nat.div_add_mod a 5, pow_add, pow_mul, hT, one_pow, one_mul]

end Algebra

section Operators

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

def sumFive (T : Module.End k V) : Module.End k V := ∑ i ∈ Finset.range 5, T ^ i

theorem sumFive_mul_sub_one {T : Module.End k V} (hT : T ^ 5 = 1) : sumFive T * (T - 1) = 0 := by
  unfold sumFive
  rw [geom_sum_mul, hT, sub_self]

theorem sumFive_mul_self {T : Module.End k V} (hT : T ^ 5 = 1) : T * sumFive T = sumFive T := by
  have h := sumFive_mul_sub_one hT
  have h2 : T * sumFive T - sumFive T = 0 := by
    have : sumFive T * (T - 1) = sumFive T * T - sumFive T := by rw [mul_sub, mul_one]
    rw [this] at h
    have hc : Commute T (sumFive T) :=
      Commute.sum_right _ _ _ fun i _ => (Commute.refl T).pow_right i
    rw [hc.eq]
    exact h
  exact sub_eq_zero.mp h2

def avgOp (T : Module.End k V) : Module.End k V := (5 : k)⁻¹ • sumFive T

theorem avgOp_apply_of_fixed (hk : (5 : k) ≠ 0) {T : Module.End k V} {w : V} (hw : T w = w) :
    avgOp T w = w := by
  have hpow : ∀ i : ℕ, (T ^ i) w = w := fun i => by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, Module.End.mul_apply, hw, ih]
  unfold avgOp sumFive
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [hpow, Finset.sum_const, Finset.card_range]
  rw [show (5 : ℕ) • w = (5 : k) • w by norm_cast]
  rw [inv_smul_smul₀ hk]

theorem mul_avgOp {T : Module.End k V} (hT : T ^ 5 = 1) : T * avgOp T = avgOp T := by
  unfold avgOp
  rw [mul_smul_comm, sumFive_mul_self hT]

theorem sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Finset.range 5, f i = ∑ a : ZMod 5, f a.val :=
  (Fin.sum_univ_eq_sum_range f 5).symm

theorem sum_range_pow_mul {A : Type*} [Ring A] {Z : A} (hZ : Z ^ 5 = 1) (c : ℕ) (hc : ¬ 5 ∣ c) :
    ∑ i ∈ Finset.range 5, Z ^ (c * i) = ∑ i ∈ Finset.range 5, Z ^ i := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hc0 : ((c : ZMod 5)) ≠ 0 := fun h => hc ((ZMod.natCast_eq_zero_iff c 5).mp h)
  rw [sum_range_eq_sum_zmod, sum_range_eq_sum_zmod]
  refine Fintype.sum_equiv (Equiv.mulLeft₀ (c : ZMod 5) hc0) _ _ fun a => ?_
  show Z ^ (c * a.val) = Z ^ ((c : ZMod 5) * a).val
  rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, pow_mod_five hZ (c * a.val)]

def tj (X Z : Module.End k V) (j : ℕ) : Module.End k V := X * Z ^ j

theorem commute_tj {X Z : Module.End k V} (hXZ : X * Z = Z * X) (j : ℕ) :
    Commute (tj X Z j) Z :=
  Commute.mul_left (show Commute X Z from hXZ) ((Commute.refl Z).pow_left j)

theorem tj_pow_five {X Z : Module.End k V} (hX : X ^ 5 = 1) (hZ : Z ^ 5 = 1)
    (hXZ : X * Z = Z * X) (j : ℕ) : (tj X Z j) ^ 5 = 1 := by
  unfold tj
  rw [Commute.mul_pow ((show Commute X Z from hXZ).pow_right _), hX, ← pow_mul, mul_comm, pow_mul,
    hZ, one_pow, one_mul]

theorem tj_add_five {X Z : Module.End k V} (hZ : Z ^ 5 = 1) (j : ℕ) :
    tj X Z (j + 5) = tj X Z j := by
  unfold tj
  rw [pow_add, hZ, mul_one]

theorem tj_add {X Z : Module.End k V} (j c : ℕ) : tj X Z (j + c) = tj X Z j * Z ^ c := by
  unfold tj
  rw [pow_add, mul_assoc]

theorem sum_range_five {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ i ∈ Finset.range 5, g i = g 0 + g 1 + g 2 + g 3 + g 4 := by
  simp [Finset.sum_range_succ]

theorem sum_avgOp_tj_apply {X Z : Module.End k V} (hk : (5 : k) ≠ 0) (hZ : Z ^ 5 = 1)
    (hXZ : X * Z = Z * X) {w : V} (hw : sumFive Z w = 0) :
    ∑ j ∈ Finset.range 5, avgOp (tj X Z j) w = w := by
  have h1 : ∀ j : ℕ, sumFive (tj X Z j) = ∑ i ∈ Finset.range 5, X ^ i * Z ^ (j * i) :=
    fun j => by
      unfold sumFive tj
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Commute.mul_pow ((show Commute X Z from hXZ).pow_right _), ← pow_mul]
  have hterm : ∀ i : ℕ, ¬ 5 ∣ i → ∑ j ∈ Finset.range 5, (X ^ i * Z ^ (j * i)) w = 0 := by
    intro i hi
    have h2 : sumFive Z = ∑ j ∈ Finset.range 5, Z ^ (j * i) := by
      unfold sumFive
      rw [← sum_range_pow_mul hZ i hi]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
    have : ∑ j ∈ Finset.range 5, (X ^ i * Z ^ (j * i)) w = (X ^ i) (sumFive Z w) := by
      rw [h2]
      simp only [Module.End.mul_apply, LinearMap.sum_apply, map_sum]
    rw [this, hw, map_zero]
  calc ∑ j ∈ Finset.range 5, avgOp (tj X Z j) w
      = (5 : k)⁻¹ • ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5, (X ^ i * Z ^ (j * i)) w := by
        simp only [avgOp, h1, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
    _ = (5 : k)⁻¹ • ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (X ^ i * Z ^ (j * i)) w := by
        rw [Finset.sum_comm]
    _ = (5 : k)⁻¹ • ((5 : ℕ) • w) := by
        congr 1
        have e0 : ∑ j ∈ Finset.range 5, (X ^ 0 * Z ^ (j * 0)) w = (5 : ℕ) • w := by simp
        rw [sum_range_five (fun i => ∑ j ∈ Finset.range 5, (X ^ i * Z ^ (j * i)) w)]
        rw [e0, hterm 1 (by decide), hterm 2 (by decide), hterm 3 (by decide),
          hterm 4 (by decide)]
        simp
    _ = w := by
        rw [show (5 : ℕ) • w = (5 : k) • w by norm_cast, inv_smul_smul₀ hk]

theorem avgOp_tj_apply_of_ne {X Z : Module.End k V} (hZ : Z ^ 5 = 1)
    (hXZ : X * Z = Z * X) {j l : ℕ} (hj : j < 5) (hl : l < 5) (hjl : l ≠ j) {w : V}
    (hw : sumFive Z w = 0) (hwj : tj X Z j w = w) : avgOp (tj X Z l) w = 0 := by
  have hc : ¬ 5 ∣ l + 5 - j := by omega
  have hl' : tj X Z l = tj X Z j * Z ^ (l + 5 - j) := by
    rw [← tj_add, show j + (l + 5 - j) = l + 5 by omega, tj_add_five hZ]
  have hcom : Commute (tj X Z j) (Z ^ (l + 5 - j)) := (commute_tj hXZ j).pow_right _
  have hfix : ∀ n : ℕ, (tj X Z j ^ n) w = w := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hwj, ih]
  have hpow : ∀ i : ℕ, (tj X Z l ^ i) w = (Z ^ ((l + 5 - j) * i)) w := by
    intro i
    rw [hl', hcom.mul_pow, (hcom.pow_pow i i).eq, Module.End.mul_apply, hfix, ← pow_mul]
  unfold avgOp sumFive
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [hpow]
  rw [← LinearMap.sum_apply, sum_range_pow_mul hZ _ hc]
  change (5 : k)⁻¹ • sumFive Z w = 0
  rw [hw, smul_zero]

end Operators

section Roots

variable {k : Type*} [Field k]

theorem four_le_natDegree_of_closed (hk : (5 : k) ≠ 0) {g : k[X]} (hg0 : g ≠ 0)
    (hg1 : ¬ IsUnit g) (hΦ : g ∣ ∑ i ∈ Finset.range 5, (X : k[X]) ^ i) {m : ℕ}
    (hm : m % 5 = 2 ∨ m % 5 = 3) (hcl : g ∣ g.comp (X ^ m)) : 4 ≤ g.natDegree := by
  classical
  obtain ⟨f, hf, hfg⟩ := WfDvdMonoid.exists_irreducible_factor hg1 hg0
  have : Fact (Irreducible f) := ⟨hf⟩
  set r : AdjoinRoot f := AdjoinRoot.root f with hrdef
  have hrg : aeval r g = 0 := by
    rw [hrdef, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hfg
  have hrΦ : aeval r (∑ i ∈ Finset.range 5, (X : k[X]) ^ i) = 0 := by
    rw [hrdef, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hfg.trans hΦ
  have hsum : ∑ i ∈ Finset.range 5, r ^ i = 0 := by
    simpa only [map_sum, map_pow, aeval_X] using hrΦ
  have hr5 : r ^ 5 = 1 := by
    have h := geom_sum_mul r 5
    rw [hsum, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  have hk5 : (5 : AdjoinRoot f) ≠ 0 := by
    intro h
    apply hk
    have h1 : (algebraMap k (AdjoinRoot f)) (5 : k) = (5 : AdjoinRoot f) := map_ofNat _ 5
    exact (algebraMap k (AdjoinRoot f)).injective (by rw [h1, h, map_zero])
  have hr1 : r ≠ 1 := by
    intro h
    rw [h] at hsum
    simp only [one_pow, Finset.sum_const, Finset.card_range] at hsum
    exact hk5 (by simpa using hsum)
  have hstep : ∀ a : AdjoinRoot f, aeval a g = 0 → aeval (a ^ m) g = 0 := by
    intro a ha
    obtain ⟨q, hq⟩ := hcl
    have h1 : aeval a (g.comp (X ^ m)) = aeval (a ^ m) g := by
      rw [aeval_comp]
      simp
    rw [← h1, hq, map_mul, ha, zero_mul]
  have hord : orderOf r = 5 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime hr5 hr1
  have hne : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ 4 → r ^ a ≠ r ^ b := by
    intro a b ha hab hb h
    have h1 : r ^ (b - a) = 1 := by
      calc r ^ (b - a) = r ^ (b - a) * r ^ 5 := by rw [hr5, mul_one]
        _ = r ^ b * r ^ (5 - a) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        _ = r ^ a * r ^ (5 - a) := by rw [h]
        _ = 1 := by rw [← pow_add, show a + (5 - a) = 5 by omega, hr5]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    have h3 := Nat.le_of_dvd (by omega) h2
    omega
  have hall : aeval (r ^ 1) g = 0 ∧ aeval (r ^ 2) g = 0 ∧ aeval (r ^ 3) g = 0 ∧
      aeval (r ^ 4) g = 0 := by
    have hr' : aeval r g = 0 := hrg
    rcases hm with h2 | h3
    · have e1 : r ^ m = r ^ 2 := by rw [pow_mod_five hr5 m, h2]
      have e2 : (r ^ 2) ^ m = r ^ 4 := by
        rw [← pow_mul, pow_mod_five hr5 (2 * m), show 2 * m % 5 = 4 by omega]
      have e3 : (r ^ 4) ^ m = r ^ 3 := by
        rw [← pow_mul, pow_mod_five hr5 (4 * m), show 4 * m % 5 = 3 by omega]
      have a2 : aeval (r ^ 2) g = 0 := e1 ▸ hstep r hr'
      have a4 : aeval (r ^ 4) g = 0 := e2 ▸ hstep _ a2
      have a3 : aeval (r ^ 3) g = 0 := e3 ▸ hstep _ a4
      exact ⟨by simpa using hr', a2, a3, a4⟩
    · have e1 : r ^ m = r ^ 3 := by rw [pow_mod_five hr5 m, h3]
      have e2 : (r ^ 3) ^ m = r ^ 4 := by
        rw [← pow_mul, pow_mod_five hr5 (3 * m), show 3 * m % 5 = 4 by omega]
      have e3 : (r ^ 4) ^ m = r ^ 2 := by
        rw [← pow_mul, pow_mod_five hr5 (4 * m), show 4 * m % 5 = 2 by omega]
      have a3 : aeval (r ^ 3) g = 0 := e1 ▸ hstep r hr'
      have a4 : aeval (r ^ 4) g = 0 := e2 ▸ hstep _ a3
      have a2 : aeval (r ^ 2) g = 0 := e3 ▸ hstep _ a4
      exact ⟨by simpa using hr', a2, a3, a4⟩
  have hcard : ({r ^ 1, r ^ 2, r ^ 3, r ^ 4} : Finset (AdjoinRoot f)).card = 4 := by
    have h12 := hne 1 2 le_rfl (by norm_num) (by norm_num)
    have h13 := hne 1 3 le_rfl (by norm_num) (by norm_num)
    have h14 := hne 1 4 le_rfl (by norm_num) (by norm_num)
    have h23 := hne 2 3 (by norm_num) (by norm_num) (by norm_num)
    have h24 := hne 2 4 (by norm_num) (by norm_num) (by norm_num)
    have h34 := hne 3 4 (by norm_num) (by norm_num) (by norm_num)
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, h13, h14⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h23, h24⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact h34), Finset.card_singleton]
  have hmap0 : g.map (algebraMap k (AdjoinRoot f)) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero]
  have hsub : ({r ^ 1, r ^ 2, r ^ 3, r ^ 4} : Finset (AdjoinRoot f)).val ⊆
      (g.map (algebraMap k (AdjoinRoot f))).roots := by
    intro a ha
    rw [Polynomial.mem_roots hmap0, Polynomial.IsRoot.def, Polynomial.eval_map, ← aeval_def]
    simp only [Finset.insert_val, Finset.singleton_val, Multiset.mem_ndinsert,
      Multiset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hall.1
    · exact hall.2.1
    · exact hall.2.2.1
    · exact hall.2.2.2
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hcard, Polynomial.natDegree_map] at this
  exact this

end Roots

section Spaces

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem pow_injective_of_mul_eq_one {Y Yi : Module.End k V} (hYiY : Yi * Y = 1) (n : ℕ) :
    Function.Injective ⇑(Y ^ n) := by
  have hYinj : Function.Injective Y := fun a b h => by
    have := congrArg Yi h
    simpa only [← Module.End.mul_apply, hYiY, Module.End.one_apply] using this
  rw [Module.End.coe_pow]
  exact hYinj.iterate n

def eSpace (X Z : Module.End k V) (j : ℕ) : Submodule k V :=
  LinearMap.ker (sumFive Z) ⊓ LinearMap.ker (tj X Z j - 1)

theorem mem_eSpace {X Z : Module.End k V} {j : ℕ} {w : V} :
    w ∈ eSpace X Z j ↔ sumFive Z w = 0 ∧ tj X Z j w = w := by
  simp only [eSpace, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]

theorem eSpace_five {X Z : Module.End k V} (hZ : Z ^ 5 = 1) : eSpace X Z 5 = eSpace X Z 0 := by
  ext w
  rw [mem_eSpace, mem_eSpace, show (5 : ℕ) = 0 + 5 from rfl, tj_add_five hZ]

theorem commute_Y_sumFive {Y Z : Module.End k V} (hYZ : Y * Z = Z * Y) :
    Commute Y (sumFive Z) :=
  Commute.sum_right _ _ _ fun i _ => (show Commute Y Z from hYZ).pow_right i

theorem Y_tj {X Z Y Yi : Module.End k V} (hYiY : Yi * Y = 1) (hYZ : Y * Z = Z * Y)
    (hYX : Y * X * Yi = X * Z) (j : ℕ) : Y * tj X Z j = tj X Z (j + 1) * Y := by
  have hYXe : Y * X = X * Z * Y := by
    calc Y * X = Y * X * (Yi * Y) := by rw [hYiY, mul_one]
      _ = (Y * X * Yi) * Y := by simp only [mul_assoc]
      _ = X * Z * Y := by rw [hYX]
  have hYZj : Y * Z ^ j = Z ^ j * Y := ((show Commute Y Z from hYZ).pow_right j).eq
  unfold tj
  calc Y * (X * Z ^ j) = (Y * X) * Z ^ j := by rw [mul_assoc]
    _ = X * Z * (Y * Z ^ j) := by rw [hYXe, mul_assoc (X * Z)]
    _ = X * Z * (Z ^ j * Y) := by rw [hYZj]
    _ = X * Z ^ (j + 1) * Y := by rw [pow_succ']; simp only [mul_assoc]

theorem Y_mem_eSpace {X Z Y Yi : Module.End k V} (hYiY : Yi * Y = 1) (hYZ : Y * Z = Z * Y)
    (hYX : Y * X * Yi = X * Z) {j : ℕ} {w : V} (hw : w ∈ eSpace X Z j) :
    Y w ∈ eSpace X Z (j + 1) := by
  rw [mem_eSpace] at hw ⊢
  refine ⟨?_, ?_⟩
  · have h := (commute_Y_sumFive hYZ).eq
    rw [← Module.End.mul_apply, ← h, Module.End.mul_apply, hw.1, map_zero]
  · have h := Y_tj hYiY hYZ hYX j
    calc tj X Z (j + 1) (Y w) = (tj X Z (j + 1) * Y) w := rfl
      _ = (Y * tj X Z j) w := by rw [h]
      _ = Y (tj X Z j w) := rfl
      _ = Y w := by rw [hw.2]

theorem Ypow_mem_eSpace {X Z Y Yi : Module.End k V} (hYiY : Yi * Y = 1) (hYZ : Y * Z = Z * Y)
    (hYX : Y * X * Yi = X * Z) {j : ℕ} {w : V} (n : ℕ) (hw : w ∈ eSpace X Z j) :
    (Y ^ n) w ∈ eSpace X Z (j + n) := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact Y_mem_eSpace hYiY hYZ hYX ih

theorem finrank_eSpace_le_succ [FiniteDimensional k V] {X Z Y Yi : Module.End k V}
    (hYiY : Yi * Y = 1) (hYZ : Y * Z = Z * Y) (hYX : Y * X * Yi = X * Z) (j : ℕ) :
    Module.finrank k (eSpace X Z j) ≤ Module.finrank k (eSpace X Z (j + 1)) := by
  have hle : (eSpace X Z j).map Y ≤ eSpace X Z (j + 1) := by
    rintro _ ⟨w, hw, rfl⟩
    exact Y_mem_eSpace hYiY hYZ hYX hw
  have hinj : Function.Injective Y := by simpa using pow_injective_of_mul_eq_one hYiY 1
  calc Module.finrank k (eSpace X Z j) = Module.finrank k ((eSpace X Z j).map Y) :=
        LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Y hinj _)
    _ ≤ Module.finrank k (eSpace X Z (j + 1)) := Submodule.finrank_mono hle

theorem commute_avgOp_sumFive {X Z : Module.End k V} (hXZ : X * Z = Z * X) (j : ℕ) :
    Commute (avgOp (tj X Z j)) (sumFive Z) := by
  unfold avgOp sumFive
  refine Commute.smul_left ?_ _
  exact Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun l _ =>
    ((commute_tj hXZ j).pow_pow i l)

theorem avgOp_mem_eSpace {X Z : Module.End k V} (hX : X ^ 5 = 1) (hZ : Z ^ 5 = 1)
    (hXZ : X * Z = Z * X) {j : ℕ} {w : V} (hw : sumFive Z w = 0) :
    avgOp (tj X Z j) w ∈ eSpace X Z j := by
  rw [mem_eSpace]
  refine ⟨?_, ?_⟩
  · have h := (commute_avgOp_sumFive hXZ j).eq
    rw [← Module.End.mul_apply, ← h, Module.End.mul_apply, hw, map_zero]
  · rw [← Module.End.mul_apply, mul_avgOp (tj_pow_five hX hZ hXZ j)]

theorem sum_finrank_eSpace_le [FiniteDimensional k V] {X Z : Module.End k V} (hk : (5 : k) ≠ 0)
    (hZ : Z ^ 5 = 1) (hXZ : X * Z = Z * X) :
    ∑ j ∈ Finset.range 5, Module.finrank k (eSpace X Z j) ≤ Module.finrank k V := by
  let Φ : (∀ j : Fin 5, eSpace X Z j.val) →ₗ[k] V :=
    ∑ j : Fin 5, (eSpace X Z j.val).subtype.comp (LinearMap.proj j)
  have hΦ : ∀ x, Φ x = ∑ j : Fin 5, (x j : V) := by
    intro x
    simp [Φ]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx0 : ∑ j : Fin 5, (x j : V) = 0 := by rw [← hΦ]; exact hx
    funext l
    apply Subtype.ext
    have h1 : avgOp (tj X Z l.val) (∑ j : Fin 5, (x j : V)) = (x l : V) := by
      rw [map_sum, Finset.sum_eq_single l]
      · exact avgOp_apply_of_fixed hk (mem_eSpace.mp (x l).2).2
      · intro j _ hjl
        exact avgOp_tj_apply_of_ne hZ hXZ j.2 l.2 (fun h => hjl (Fin.ext h.symm))
          (mem_eSpace.mp (x j).2).1 (mem_eSpace.mp (x j).2).2
      · intro h
        exact absurd (Finset.mem_univ l) h
    rw [hx0, map_zero] at h1
    exact h1.symm
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi_fintype] at h
  rw [Finset.sum_range (fun j => Module.finrank k (eSpace X Z j))]
  exact h

end Spaces

section Final

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem ker_sumFive_ne_bot {Z : Module.End k V} (hZ : Z ^ 5 = 1) (hZ1 : Z ≠ 1) :
    LinearMap.ker (sumFive Z) ≠ ⊥ := by
  intro h
  apply hZ1
  have hinj : Function.Injective (sumFive Z) := LinearMap.ker_eq_bot.mp h
  have h0 : sumFive Z * (Z - 1) = 0 := sumFive_mul_sub_one hZ
  have : Z - 1 = 0 := by
    ext v
    apply hinj
    have := congrArg (fun f : Module.End k V => f v) h0
    simpa using this
  exact sub_eq_zero.mp this

theorem eSpace_zero_ne_bot {X Z Y Yi : Module.End k V} (hk : (5 : k) ≠ 0) (hX : X ^ 5 = 1)
    (hZ : Z ^ 5 = 1) (hXZ : X * Z = Z * X) (hYiY : Yi * Y = 1) (hYZ : Y * Z = Z * Y)
    (hYX : Y * X * Yi = X * Z) (hWne : LinearMap.ker (sumFive Z) ≠ ⊥) :
    eSpace X Z 0 ≠ ⊥ := by
  intro h0
  apply hWne
  rw [eq_bot_iff]
  intro w hw
  have hw' : sumFive Z w = 0 := LinearMap.mem_ker.mp hw
  have hsum := sum_avgOp_tj_apply hk hZ hXZ hw'
  have hterm : ∀ j ∈ Finset.range 5, avgOp (tj X Z j) w = 0 := by
    intro j hj
    have hj5 : j < 5 := Finset.mem_range.mp hj
    have hmem := avgOp_mem_eSpace hX hZ hXZ (j := j) hw'
    have hY := Ypow_mem_eSpace hYiY hYZ hYX (5 - j) hmem
    rw [show j + (5 - j) = 5 by omega, eSpace_five hZ, h0] at hY
    have h1 : (Y ^ (5 - j)) (avgOp (tj X Z j) w) = 0 := Submodule.mem_bot k |>.mp hY
    exact pow_injective_of_mul_eq_one hYiY (5 - j) (by rw [h1, map_zero])
  rw [← hsum, Finset.sum_eq_zero hterm]
  exact Submodule.zero_mem _

end Final

section Main

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem aeval_conj {H Hi a : Module.End k V} (hHiH : Hi * H = 1) (hHHi : H * Hi = 1) (p : k[X]) :
    aeval (H * a * Hi) p = H * aeval a p * Hi := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial n c =>
    have hpow : ∀ n : ℕ, (H * a * Hi) ^ n = H * a ^ n * Hi := by
      intro n
      induction n with
      | zero => simp [hHHi]
      | succ n ih =>
        calc (H * a * Hi) ^ (n + 1) = (H * a ^ n * Hi) * (H * a * Hi) := by rw [pow_succ, ih]
          _ = H * a ^ n * (Hi * H) * (a * Hi) := by simp only [mul_assoc]
          _ = H * a ^ (n + 1) * Hi := by rw [hHiH, mul_one, pow_succ]; simp only [mul_assoc]
    rw [aeval_monomial, aeval_monomial, hpow]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]

theorem pow_mem_of_mem {Z : Module.End k V} {N : Submodule k V} (hZN : ∀ w ∈ N, Z w ∈ N)
    (n : ℕ) : ∀ w ∈ N, (Z ^ n) w ∈ N := by
  induction n with
  | zero => intro w hw; simpa using hw
  | succ n ih => intro w hw; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hZN w hw)

theorem finrank_ge_twenty_of_heisenberg [FiniteDimensional k V] (hk : (5 : k) ≠ 0)
    {X Z Y Yi H Hi : Module.End k V} (hYiY : Yi * Y = 1) (hHiH : Hi * H = 1) (hHHi : H * Hi = 1)
    (hX : X ^ 5 = 1) (hZ : Z ^ 5 = 1) (hXZ : X * Z = Z * X) (hYZ : Y * Z = Z * Y)
    (hYX : Y * X * Yi = X * Z) {m : ℕ} (hm : m % 5 = 2 ∨ m % 5 = 3)
    (hHZ : H * Z * Hi = Z ^ m) (hZ1 : Z ≠ 1) : 20 ≤ Module.finrank k V := by
  classical
  have hm5 : ¬ 5 ∣ m := by omega
  have hWne : LinearMap.ker (sumFive Z) ≠ ⊥ := ker_sumFive_ne_bot hZ hZ1
  have hNne : eSpace X Z 0 ≠ ⊥ := eSpace_zero_ne_bot hk hX hZ hXZ hYiY hYZ hYX hWne
  have hchain : ∀ n : ℕ, Module.finrank k (eSpace X Z 0) ≤ Module.finrank k (eSpace X Z n) := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact ih.trans (finrank_eSpace_le_succ hYiY hYZ hYX n)
  have hsum := sum_finrank_eSpace_le hk hZ hXZ
  have h5 : 5 * Module.finrank k (eSpace X Z 0) ≤
      ∑ j ∈ Finset.range 5, Module.finrank k (eSpace X Z j) := by
    calc 5 * Module.finrank k (eSpace X Z 0)
        = ∑ j ∈ Finset.range 5, Module.finrank k (eSpace X Z 0) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => hchain j
  have h4 : 4 ≤ Module.finrank k (eSpace X Z 0) := by
    set N := eSpace X Z 0 with hNdef
    have hZN : ∀ w ∈ N, Z w ∈ N := by
      intro w hw
      rw [hNdef, mem_eSpace] at hw ⊢
      refine ⟨?_, ?_⟩
      · have h : Commute Z (sumFive Z) :=
          Commute.sum_right _ _ _ fun i _ => (Commute.refl Z).pow_right i
        rw [← Module.End.mul_apply, ← h.eq, Module.End.mul_apply, hw.1, map_zero]
      · have h := (commute_tj hXZ 0).eq
        rw [← Module.End.mul_apply, h, Module.End.mul_apply, hw.2]
    have hZm : ∀ x ∈ N, (Z ^ m) x ∈ N := pow_mem_of_mem hZN m
    have hNnt : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hNne
    set T : Module.End k N := Z.restrict hZN with hTdef
    set g : k[X] := minpoly k T with hgdef
    have hint : IsIntegral k T := IsIntegral.of_finite k T
    have hg0 : g ≠ 0 := minpoly.ne_zero hint
    have hg1 : ¬ IsUnit g := minpoly.not_isUnit k T
    have hdeg : g.natDegree ≤ Module.finrank k N := by
      have h1 := LinearMap.minpoly_dvd_charpoly T
      have h2 := Polynomial.natDegree_le_of_dvd h1 (LinearMap.charpoly_monic T).ne_zero
      rwa [LinearMap.charpoly_natDegree] at h2
    have hNW : ∀ w ∈ N, sumFive Z w = 0 := fun w hw => ((mem_eSpace.mp hw).1)
    have hΦ : g ∣ ∑ i ∈ Finset.range 5, (Polynomial.X : k[X]) ^ i := by
      apply minpoly.dvd
      ext ⟨w, hw⟩
      have h1 := CFSG.LinearAlgebra.coe_aeval_restrict_apply hZN
        (∑ i ∈ Finset.range 5, (Polynomial.X : k[X]) ^ i) ⟨w, hw⟩
      have h2 : aeval Z (∑ i ∈ Finset.range 5, (Polynomial.X : k[X]) ^ i) = sumFive Z := by
        simp [sumFive, map_sum]
      rw [h2, hNW w hw] at h1
      exact h1
    have hgN : ∀ x : V, x ∈ N → aeval Z g x = 0 := by
      intro x hx
      have h1 := CFSG.LinearAlgebra.coe_aeval_restrict_apply hZN g ⟨x, hx⟩
      have h2 : aeval T g = 0 := minpoly.aeval k T
      rw [← h1, h2]
      rfl
    have hgW : ∀ w : V, sumFive Z w = 0 → aeval Z g w = 0 := by
      intro w hw
      have hsum' := sum_avgOp_tj_apply hk hZ hXZ hw
      have hterm : ∀ j ∈ Finset.range 5, aeval Z g (avgOp (tj X Z j) w) = 0 := by
        intro j hj
        have hj5 : j < 5 := Finset.mem_range.mp hj
        have hmem := avgOp_mem_eSpace hX hZ hXZ (j := j) hw
        have hY := Ypow_mem_eSpace hYiY hYZ hYX (5 - j) hmem
        rw [show j + (5 - j) = 5 by omega, eSpace_five hZ] at hY
        have hk0 := hgN _ hY
        have hcomm : Commute (Y ^ (5 - j)) (aeval Z g) :=
          (CFSG.LinearAlgebra.commute_aeval_of_commute (show Commute Y Z from hYZ) g).pow_left _
        have h3 : (Y ^ (5 - j)) (aeval Z g (avgOp (tj X Z j) w)) = 0 := by
          rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
          exact hk0
        exact pow_injective_of_mul_eq_one hYiY (5 - j) (by rw [h3, map_zero])
      rw [← hsum', map_sum]
      exact Finset.sum_eq_zero hterm
    have hΦpoly : aeval Z (∑ i ∈ Finset.range 5, (Polynomial.X : k[X]) ^ i) = sumFive Z := by
      simp [sumFive, map_sum]
    have hS_conj : H * sumFive Z * Hi = sumFive Z := by
      have h1 := aeval_conj (a := Z) hHiH hHHi (∑ i ∈ Finset.range 5, (Polynomial.X : k[X]) ^ i)
      rw [hΦpoly, hHZ] at h1
      have h2 : aeval (Z ^ m) (∑ i ∈ Finset.range 5, (Polynomial.X : k[X]) ^ i) = sumFive Z := by
        simp only [sumFive, map_sum, map_pow, aeval_X, ← pow_mul]
        exact sum_range_pow_mul hZ m hm5
      rw [h2] at h1
      exact h1.symm
    have hHW : ∀ w, sumFive Z w = 0 → sumFive Z (Hi w) = 0 := by
      intro w hw
      have h1 : sumFive Z * Hi = Hi * sumFive Z := by
        calc sumFive Z * Hi = (Hi * H) * sumFive Z * Hi := by rw [hHiH, one_mul]
          _ = Hi * (H * sumFive Z * Hi) := by simp only [mul_assoc]
          _ = Hi * sumFive Z := by rw [hS_conj]
      rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hw, map_zero]
    have hgm : ∀ w : V, sumFive Z w = 0 → aeval (Z ^ m) g w = 0 := by
      intro w hw
      have h1 := aeval_conj (a := Z) hHiH hHHi g
      rw [hHZ] at h1
      rw [h1, Module.End.mul_apply, Module.End.mul_apply, hgW _ (hHW w hw), map_zero]
    have hcl : g ∣ g.comp (Polynomial.X ^ m) := by
      apply minpoly.dvd
      ext ⟨w, hw⟩
      rw [aeval_comp]
      have e : aeval T (Polynomial.X ^ m : k[X]) = T ^ m := by simp
      rw [e, hTdef, Module.End.pow_restrict m hZN hZm]
      have h1 := CFSG.LinearAlgebra.coe_aeval_restrict_apply hZm g ⟨w, hw⟩
      rw [h1, hgm w (hNW w hw)]
      rfl
    exact (four_le_natDegree_of_closed hk hg0 hg1 hΦ hm hcl).trans hdeg
  omega

end Main

end CFSG.RankThree.PartOne.HNRed
