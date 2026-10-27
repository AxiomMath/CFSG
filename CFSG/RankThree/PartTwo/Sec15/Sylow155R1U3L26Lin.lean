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
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open Polynomial

private theorem four_dvd_of_pow_five_modEq {m : ℕ} (h : 5 ^ m ≡ 1 [MOD 13]) : 4 ∣ m := by
  have h4 : orderOf (5 : ZMod 13) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  have h5 : (5 : ZMod 13) ^ m = 1 := by
    have := (ZMod.natCast_eq_natCast_iff (5 ^ m) 1 13).2 h
    simpa using this
  rw [← h4]
  exact orderOf_dvd_of_pow_eq_one h5

private theorem four_dvd_finrank_of_stable {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]
    [Module.Finite (ZMod 5) V] {g : Module.End (ZMod 5) V} (hg : g ^ 13 = 1)
    {U : Submodule (ZMod 5) V} (hU : ∀ u ∈ U, g u ∈ U) (hfix : ∀ u ∈ U, g u = u → u = 0) :
    4 ∣ Module.finrank (ZMod 5) U := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  classical
  have : Finite U := Module.finite_of_finite (ZMod 5)
  have : Fintype U := Fintype.ofFinite U
  let f : Function.End U := fun u => ⟨g u, hU u u.2⟩
  have hfpow : ∀ (n : ℕ) (u : U), (((f ^ n) u : U) : V) = (g ^ n) u := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ f n, pow_succ g n]
      exact ih (f u)
  have hf : f ^ 13 ^ 1 = 1 := by
    funext u
    apply Subtype.ext
    rw [pow_one, hfpow, hg]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  have hfp : Fintype.card f.fixedPoints = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, ?_⟩, ?_⟩
    · show f 0 = 0
      apply Subtype.ext
      simp [f]
    · rintro ⟨u, hu⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hfix u u.2 (congrArg Subtype.val hu)
  rw [hfp, Module.card_eq_pow_finrank (K := ZMod 5), ZMod.card] at hmod
  exact four_dvd_of_pow_five_modEq hmod

private theorem mul_aeval_eq {A : Type*} [Ring A] [Algebra (ZMod 5) A] {x g h : A}
    (hxg : x * g = h * x) (P : (ZMod 5)[X]) : x * aeval g P = aeval h P * x := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, mul_add, add_mul, hp, hq]
  | monomial n a =>
    have hpow : x * g ^ n = h ^ n * x := SemiconjBy.pow_right hxg n
    have hc : x * algebraMap (ZMod 5) A a = algebraMap (ZMod 5) A a * x :=
      (Algebra.commutes a x).symm
    rw [aeval_monomial, aeval_monomial]
    calc x * (algebraMap (ZMod 5) A a * g ^ n) = (x * algebraMap (ZMod 5) A a) * g ^ n := by
          rw [mul_assoc]
      _ = algebraMap (ZMod 5) A a * (x * g ^ n) := by rw [hc, mul_assoc]
      _ = algebraMap (ZMod 5) A a * (h ^ n * x) := by rw [hpow]
      _ = algebraMap (ZMod 5) A a * h ^ n * x := by rw [mul_assoc]

private theorem aeval_pow_five {A : Type*} [Semiring A] [Algebra (ZMod 5) A] (T : A)
    (P : (ZMod 5)[X]) : aeval (T ^ 5) P = aeval T P ^ 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [← expand_aeval, ZMod.expand_card, map_pow]

open scoped IsMulCommutative in
private theorem false_of_finrank_four {W : Type*} [AddCommGroup W] [Module (ZMod 5) W]
    [Module.Finite (ZMod 5) W] (hW : Module.finrank (ZMod 5) W = 4)
    {g x : Module.End (ZMod 5) W} (hg : g ^ 13 = 1) (hfix : ∀ w, g w = w → w = 0)
    (hx : Function.Injective x) (hxg : x * g = g ^ 3 * x) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  classical
  have hpos : 0 < Module.finrank (ZMod 5) W := by omega
  have : Nontrivial W := Module.finrank_pos_iff.1 hpos
  obtain ⟨w₀, hw₀⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hg1 : g ≠ 1 := fun h => hw₀ (hfix w₀ (by rw [h]; rfl))
  have hord : orderOf g = 13 := orderOf_eq_prime hg hg1
  have hfin : IsOfFinOrder g := orderOf_pos_iff.1 (by omega)
  have hirr : ∀ U : Submodule (ZMod 5) W, (∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have h4 := four_dvd_finrank_of_stable hg hU (fun u _ hu => hfix u hu)
    have hle : Module.finrank (ZMod 5) U ≤ 4 := hW ▸ Submodule.finrank_le U
    have h04 : Module.finrank (ZMod 5) U = 0 ∨ Module.finrank (ZMod 5) U = 4 := by omega
    rcases h04 with h0 | h0
    · exact Or.inl (Submodule.finrank_eq_zero.1 h0)
    · exact Or.inr (Submodule.eq_top_of_finrank_eq (h0.trans hW.symm))
  set K : Subalgebra (ZMod 5) (Module.End (ZMod 5) W) := Algebra.adjoin (ZMod 5) {g}
  have hgK : g ∈ K := Algebra.self_mem_adjoin_singleton (ZMod 5) g
  have hinj : ∀ k : K, k ≠ 0 → Function.Injective (k : Module.End (ZMod 5) W) := by
    intro k hk0
    have hcomm : Commute g (k : Module.End (ZMod 5) W) :=
      Algebra.commute_of_mem_adjoin_self k.2
    have hk0' : (k : Module.End (ZMod 5) W) ≠ 0 := fun h => hk0 (Subtype.ext h)
    have hker : ∀ u ∈ LinearMap.ker (k : Module.End (ZMod 5) W),
        g u ∈ LinearMap.ker (k : Module.End (ZMod 5) W) := by
      intro u hu
      rw [LinearMap.mem_ker] at hu ⊢
      have h := LinearMap.congr_fun hcomm.eq u
      rw [Module.End.mul_apply, Module.End.mul_apply, hu, map_zero] at h
      exact h.symm
    rcases hirr _ hker with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) hk0'
  have : IsMulCommutative K := Algebra.isMulCommutative_adjoin_singleton (ZMod 5) g
  let : CommRing K := inferInstance
  have : NoZeroDivisors K := ⟨fun {a b} hab => by
    by_contra h
    rw [not_or] at h
    have hmul : Function.Injective ((a : Module.End (ZMod 5) W) * (b : Module.End (ZMod 5) W)) :=
      fun u v huv => hinj b h.2 (hinj a h.1 huv)
    have h0 : (a : Module.End (ZMod 5) W) * (b : Module.End (ZMod 5) W) = 0 :=
      congrArg Subtype.val hab
    rw [h0] at hmul
    exact hw₀ (hmul (a₁ := w₀) (a₂ := 0) (by simp))⟩
  have : IsDomain K := NoZeroDivisors.to_isDomain K
  set χ : (ZMod 5)[X] := LinearMap.charpoly g
  have hχmonic : χ.Monic := LinearMap.charpoly_monic g
  have hχdeg : χ.natDegree = 4 := (LinearMap.charpoly_natDegree g).trans hW
  have hr1 : aeval g χ = 0 := LinearMap.aeval_self_charpoly g
  have hr3 : aeval (g ^ 3) χ = 0 := by
    have h := mul_aeval_eq hxg χ
    rw [hr1, mul_zero] at h
    ext v
    obtain ⟨u, rfl⟩ := (LinearMap.injective_iff_surjective.1 hx) v
    have := LinearMap.congr_fun h u
    simpa [Module.End.mul_apply] using this.symm
  have hr5 : aeval (g ^ 5) χ = 0 := by
    rw [aeval_pow_five, hr1]
    simp
  have hr12 : aeval (g ^ 12) χ = 0 := by
    have h25 : g ^ 25 = g ^ 12 := by
      calc g ^ 25 = g ^ 12 * g ^ 13 := by rw [← pow_add]
        _ = g ^ 12 := by rw [hg, mul_one]
    rw [← h25, show 25 = 5 * 5 from rfl, pow_mul, aeval_pow_five, hr5]
    simp
  have hr8 : aeval (g ^ 8) χ = 0 := by
    have h60 : g ^ 60 = g ^ 8 := by
      calc g ^ 60 = g ^ 8 * (g ^ 13) ^ 4 := by rw [← pow_mul, ← pow_add]
        _ = g ^ 8 := by rw [hg, one_pow, mul_one]
    rw [← h60, show 60 = 12 * 5 from rfl, pow_mul, aeval_pow_five, hr12]
    simp
  let z : ℕ → K := fun k => ⟨g ^ k, pow_mem hgK k⟩
  let S : Finset ℕ := {1, 3, 5, 8, 12}
  let Z : Finset K := S.image z
  have hzinj : Set.InjOn z (S : Set ℕ) := by
    intro i hi j hj hij
    have hij' : g ^ i = g ^ j := congrArg Subtype.val hij
    have hmod : i ≡ j [MOD 13] := by
      rw [← hord]
      exact hfin.pow_eq_pow_iff_modEq.1 hij'
    have hi' : i < 13 := by
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hi
      omega
    have hj' : j < 13 := by
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hj
      omega
    exact hmod.eq_of_lt_of_lt hi' hj'
  have hZcard : Z.card = 5 := by
    rw [Finset.card_image_of_injOn hzinj]
    rfl
  set p : K[X] := χ.map (algebraMap (ZMod 5) K) with hp
  have hpmonic : p.Monic := hχmonic.map _
  have hpdeg : p.natDegree = 4 := by
    rw [hp, hχmonic.natDegree_map, hχdeg]
  have hroot : ∀ k, aeval (g ^ k) χ = 0 → z k ∈ p.roots := by
    intro k hk
    rw [mem_roots hpmonic.ne_zero, IsRoot, hp, eval_map]
    change eval₂ (algebraMap (ZMod 5) K) (z k) χ = 0
    rw [← aeval_def]
    apply Subtype.ext
    simp [z, hk]
  have hZsub : Z.val ⊆ p.roots := by
    intro a ha
    rw [Finset.mem_val] at ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 ha
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact hroot 1 (by simpa using hr1)
    · exact hroot 3 hr3
    · exact hroot 5 hr5
    · exact hroot 8 hr8
    · exact hroot 12 hr12
  have hle := Polynomial.card_le_degree_of_subset_roots hZsub
  rw [hZcard, hpdeg] at hle
  omega

theorem false_of_pow_thirteen_conj_cube {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]
    [Module.Finite (ZMod 5) V] (hdim : Module.finrank (ZMod 5) V ≤ 7)
    {γ ξ : V →ₗ[ZMod 5] V} (hγ : γ ^ 13 = 1) (hγ1 : γ ≠ 1) (hξ : IsUnit ξ)
    (hξγ : ξ * γ = γ ^ 3 * ξ) : False := by
  have h13ne : ((13 : ℕ) : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let W : Submodule (ZMod 5) V := LinearMap.range (γ - 1)
  have hγW : ∀ w ∈ W, γ w ∈ W := by
    rintro _ ⟨v, rfl⟩
    exact ⟨γ v, by simp⟩
  have hfixW : ∀ w ∈ W, γ w = w → w = 0 := by
    rintro _ ⟨v, rfl⟩ hw
    set w := (γ - 1) v with hwdef
    have hγv : γ v = v + w := by simp [hwdef]
    have hk : ∀ n : ℕ, (γ ^ n) v = v + (n : ZMod 5) • w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, hw, hγv, Nat.cast_succ,
          add_smul, one_smul]
        abel
    have h13 : ((13 : ℕ) : ZMod 5) • w = 0 := by
      have := hk 13
      rw [hγ, Module.End.one_apply] at this
      exact add_eq_left.1 this.symm
    rcases smul_eq_zero.1 h13 with h | h
    · exact absurd h h13ne
    · exact h
  have hWne : W ≠ ⊥ := by
    intro h
    exact hγ1 (sub_eq_zero.1 (LinearMap.range_eq_bot.1 h))
  have hξW : ∀ w ∈ W, ξ w ∈ W := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(∑ i ∈ Finset.range 3, γ ^ i) (ξ v), ?_⟩
    have h : ξ * (γ - 1) = (γ - 1) * (∑ i ∈ Finset.range 3, γ ^ i) * ξ := by
      rw [mul_geom_sum, mul_sub, mul_one, hξγ, sub_mul, one_mul]
    have := LinearMap.congr_fun h v
    simp only [Module.End.mul_apply] at this
    exact this.symm
  have hfin : Module.finrank (ZMod 5) W = 4 := by
    have h4 := four_dvd_finrank_of_stable hγ hγW hfixW
    have hle : Module.finrank (ZMod 5) W ≤ 7 := (Submodule.finrank_le W).trans hdim
    have hpos : 0 < Module.finrank (ZMod 5) W :=
      Nat.pos_of_ne_zero fun h => hWne (Submodule.finrank_eq_zero.1 h)
    omega
  obtain ⟨γW, hγWc⟩ : ∃ γW : Module.End (ZMod 5) W, ∀ w : W, (γW w : V) = γ w :=
    ⟨γ.restrict hγW, fun w => rfl⟩
  obtain ⟨ξW, hξWc⟩ : ∃ ξW : Module.End (ZMod 5) W, ∀ w : W, (ξW w : V) = ξ w :=
    ⟨ξ.restrict hξW, fun w => rfl⟩
  have hpowW : ∀ (n : ℕ) (w : W), ((γW ^ n) w : V) = (γ ^ n) w := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hγWc]
  have hgW : γW ^ 13 = 1 := by
    ext w
    rw [hpowW, hγ]
    rfl
  have hfixWW : ∀ w : W, γW w = w → w = 0 := by
    intro w hw
    apply Subtype.ext
    exact hfixW w w.2 ((hγWc w).symm.trans (congrArg Subtype.val hw))
  have hξinj : Function.Injective ξ := ((Module.End.isUnit_iff ξ).1 hξ).1
  have hxW : Function.Injective ξW := by
    intro a b hab
    apply Subtype.ext
    apply hξinj
    rw [← hξWc, ← hξWc, hab]
  have hxgW : ξW * γW = γW ^ 3 * ξW := by
    ext w
    have h := LinearMap.congr_fun hξγ (w : V)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h
    rw [Module.End.mul_apply, Module.End.mul_apply, hξWc, hγWc, hpowW, hξWc]
    exact h
  exact false_of_finrank_four hfin hgW hfixWW hxW hxgW

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
