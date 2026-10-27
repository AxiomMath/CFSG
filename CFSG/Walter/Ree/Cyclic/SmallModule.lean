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
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public noncomputable section

namespace CFSG.Walter.Ree.Cyclic

open Module

variable {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem natCard_modEq_natCard_inf_ker {p k : ℕ} [Fact p.Prime] {f : Module.End K W}
    (hf : f ^ p ^ k = 1) {N : Submodule K W} (hN : ∀ v ∈ N, f v ∈ N) :
    Nat.card N ≡ Nat.card ↥(N ⊓ LinearMap.ker (f - 1)) [MOD p] := by
  classical
  have : Finite W := Module.finite_of_finite K
  have : Fintype W := Fintype.ofFinite W
  let g : Function.End N := fun v => ⟨f v, hN v v.2⟩
  have hg : ∀ (m : ℕ) (v : N), ((g ^ m) v : W) = (f ^ m) v := by
    intro m
    induction m with
    | zero => intro v; rfl
    | succ m ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply]
      exact ih (g v)
  have hg1 : g ^ p ^ k = 1 := by
    funext v
    exact Subtype.ext ((hg _ v).trans (by rw [hf]; rfl))
  have h := Equiv.Perm.card_fixedPoints_modEq hg1
  let e : Function.fixedPoints g ≃ ↥(N ⊓ LinearMap.ker (f - 1)) :=
    { toFun := fun v => ⟨v.1.1, Submodule.mem_inf.2 ⟨v.1.2, LinearMap.mem_ker.2 (by
        have hv : f v.1.1 = v.1.1 := congrArg Subtype.val v.2
        rw [LinearMap.sub_apply, Module.End.one_apply, hv, sub_self])⟩⟩
      invFun := fun w => ⟨⟨w.1, (Submodule.mem_inf.1 w.2).1⟩, by
        have hw : (f - 1) w.1 = 0 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 w.2).2
        rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
        exact Subtype.ext hw⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_congr e] at h

theorem orderOf_dvd_finrank_sub {p k : ℕ} [Fact p.Prime] {f : Module.End K W}
    (hf : f ^ p ^ k = 1) {N : Submodule K W} (hN : ∀ v ∈ N, f v ∈ N)
    (hq : IsUnit (Nat.card K : ZMod p)) :
    orderOf (Nat.card K : ZMod p) ∣
      finrank K N - finrank K ↥(N ⊓ LinearMap.ker (f - 1)) := by
  have h := natCard_modEq_natCard_inf_ker hf hN
  rw [Module.natCard_eq_pow_finrank (K := K) (V := N),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥(N ⊓ LinearMap.ker (f - 1))),
    ← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_pow] at h
  have hle : finrank K ↥(N ⊓ LinearMap.ker (f - 1)) ≤ finrank K N :=
    Submodule.finrank_mono inf_le_left
  apply orderOf_dvd_of_pow_eq_one
  refine (hq.pow (finrank K ↥(N ⊓ LinearMap.ker (f - 1)))).mul_left_cancel ?_
  rw [← pow_add, Nat.add_sub_cancel' hle, mul_one, h]

theorem injective_of_commute {p k : ℕ} [Fact p.Prime] {f : Module.End K W}
    (hf : f ^ p ^ k = 1) (hfix : LinearMap.ker (f - 1) = ⊥)
    (hW : finrank K W = orderOf (Nat.card K : ZMod p)) {T : Module.End K W}
    (hT : Commute T f) (hT0 : T ≠ 0) : Function.Injective T := by
  have hpos : 0 < finrank K W := by
    refine Nat.pos_of_ne_zero fun h0 => hT0 ?_
    have : Subsingleton W := Module.finrank_zero_iff.1 h0
    exact Subsingleton.elim _ _
  have hq : IsUnit (Nat.card K : ZMod p) := (orderOf_pos_iff.1 (hW ▸ hpos)).isUnit
  have hN : ∀ v ∈ LinearMap.ker T, f v ∈ LinearMap.ker T := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, hT.eq, Module.End.mul_apply, hv, map_zero]
  have h := orderOf_dvd_finrank_sub hf hN hq
  rw [hfix, inf_bot_eq, finrank_bot, Nat.sub_zero, ← hW] at h
  rw [← LinearMap.ker_eq_bot]
  by_contra hne
  have h0 : 0 < finrank K (LinearMap.ker T) :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.1 h)
  have htop : finrank K (LinearMap.ker T) = finrank K W :=
    le_antisymm (Submodule.finrank_le _) (Nat.le_of_dvd h0 h)
  exact hT0 (LinearMap.ker_eq_top.1 (Submodule.eq_top_of_finrank_eq htop))

theorem isCyclic_of_commute {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    {f : Module.End K W} (hf : f ^ p ^ k = 1) (hfix : LinearMap.ker (f - 1) = ⊥)
    (hW : finrank K W = orderOf (Nat.card K : ZMod p)) (hpos : 0 < finrank K W)
    (ρ : G →* Module.End K W) (hρ : Function.Injective ρ) (hcomm : ∀ g, Commute (ρ g) f) :
    IsCyclic G := by
  let C : Subalgebra K (Module.End K W) := Subalgebra.centralizer K {f}
  have hmem : ∀ g, ρ g ∈ C := fun g => by
    rw [Subalgebra.mem_centralizer_iff]
    rintro h rfl
    exact (hcomm g).eq.symm
  have hinj : ∀ T : C, T ≠ 0 → Function.Injective (T : Module.End K W) := by
    intro T hT
    refine injective_of_commute hf hfix hW ?_ fun h => hT (Subtype.ext h)
    exact ((Subalgebra.mem_centralizer_iff K).1 T.2 f (Set.mem_singleton f)).symm
  have : Nontrivial W := Module.nontrivial_of_finrank_pos hpos
  have : Nontrivial C := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  have : NoZeroDivisors C := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · refine Or.inr (Subtype.ext (LinearMap.ext fun v => hinj a ha ?_))
      have := congrArg (fun T : C => (T : Module.End K W) v) hab
      simpa using this⟩
  have : IsDomain C := NoZeroDivisors.to_isDomain C
  have : Finite (Module.End K W) := Module.finite_of_finite K
  have : Finite C := Subtype.finite
  let : Field C := (Finite.isDomain_to_isField C).toField
  let ρC : G →* C :=
    { toFun := fun g => ⟨ρ g, hmem g⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun g h => Subtype.ext (map_mul ρ g h) }
  exact isCyclic_of_injective_ringHom ρC fun g h hgh => hρ (congrArg Subtype.val hgh)

theorem eq_of_dvd_of_lt_two_mul {e m : ℕ} (h : e ∣ m) (h0 : 0 < m) (h2 : m < 2 * e) : m = e := by
  obtain ⟨c, rfl⟩ := h
  rcases c with _ | _ | c
  · simp at h0
  · simp
  · have : e * 2 ≤ e * (c + 1 + 1) := Nat.mul_le_mul_left e (by omega)
    omega

theorem isCyclic_of_isPGroup_of_finrank_lt {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hG : IsPGroup p G) (ρ : G →* Module.End K W) (hρ : Function.Injective ρ)
    (hW : finrank K W < 2 * orderOf (Nat.card K : ZMod p)) : IsCyclic G := by
  obtain ⟨e, he⟩ : ∃ e, orderOf (Nat.card K : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hW
  have hq : IsUnit (Nat.card K : ZMod p) := (orderOf_pos_iff.1 (by omega)).isUnit
  have hpow : ∀ g : G, ∃ k : ℕ, ρ g ^ p ^ k = 1 := fun g => by
    obtain ⟨k, hk⟩ := hG g
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hfixdim : ∀ g : G, g ≠ 1 → finrank K (LinearMap.ker (ρ g - 1)) + e ≤ finrank K W := by
    intro g hg
    obtain ⟨k, hk⟩ := hpow g
    have h := orderOf_dvd_finrank_sub hk (N := ⊤) (fun _ _ => trivial) hq
    rw [top_inf_eq, finrank_top, he] at h
    have hlt : finrank K (LinearMap.ker (ρ g - 1)) < finrank K W := by
      refine Submodule.finrank_lt fun htop => hg (hρ ?_)
      rw [map_one]
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ LinearMap.ker (ρ g - 1) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      rw [hv, Module.End.one_apply]
    have := Nat.le_of_dvd (by omega) h
    omega
  rcases subsingleton_or_nontrivial G with hsub | hnt
  · exact isCyclic_of_subsingleton
  have := hG.center_nontrivial
  obtain ⟨⟨x, hxc⟩, hx1⟩ := exists_ne (1 : Subgroup.center G)
  have hx : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxg : ∀ g : G, g * x = x * g := Subgroup.mem_center_iff.1 hxc
  have hcomm : ∀ g : G, Commute (ρ g) (ρ x) := fun g => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hxg g]
  obtain ⟨k, hxk⟩ := hG x
  have hk : ρ x ^ p ^ k = 1 := by rw [← map_pow, hxk, map_one]
  let U : Submodule K W := LinearMap.range (ρ x - 1)
  have hU : ∀ g : G, ∀ v ∈ U, ρ g v ∈ U := by
    intro g v hv
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hv
    refine LinearMap.mem_range.2 ⟨ρ g w, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, mul_sub, sub_mul, mul_one, one_mul,
      (hcomm g).eq]
  have hxle := hfixdim x hx
  have hrank := LinearMap.finrank_range_add_finrank_ker (ρ x - 1)
  have hUdim : finrank K U = e := by
    have h := orderOf_dvd_finrank_sub hk (N := ⊤) (fun _ _ => trivial) hq
    rw [top_inf_eq, finrank_top, he] at h
    have := eq_of_dvd_of_lt_two_mul h (by omega) (by omega)
    change finrank K (LinearMap.range (ρ x - 1)) = e
    omega
  have hUfix : U ⊓ LinearMap.ker (ρ x - 1) = ⊥ := by
    have h := orderOf_dvd_finrank_sub hk (N := U) (hU x) hq
    rw [hUdim, he] at h
    have hle : finrank K ↥(U ⊓ LinearMap.ker (ρ x - 1)) ≤ finrank K (LinearMap.ker (ρ x - 1)) :=
      Submodule.finrank_mono inf_le_right
    refine Submodule.finrank_eq_zero.1 ?_
    by_contra hne
    have := Nat.eq_zero_of_dvd_of_lt h (by omega)
    omega
  let ρU : G →* Module.End K U :=
    { toFun := fun g => (ρ g).restrict (hU g)
      map_one' := by
        ext v
        simp
      map_mul' := fun g h => by
        ext v
        simp }
  have hρU : ∀ g (v : U), (ρU g v : W) = ρ g v := fun _ _ => rfl
  have hρUinj : Function.Injective ρU := by
    refine (injective_iff_map_eq_one ρU).2 fun g hg => ?_
    by_contra hg1
    have hgle := hfixdim g hg1
    have hsub : U ≤ LinearMap.ker (ρ g - 1) := fun v hv => by
      have := congrArg (fun T : Module.End K U => (T ⟨v, hv⟩ : W)) hg
      simp only [hρU, Module.End.one_apply] at this
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, this, sub_self]
    have := Submodule.finrank_mono hsub
    omega
  refine isCyclic_of_commute (k := k) (f := ρU x) ?_ ?_ (hUdim.trans he.symm) (by omega) ρU
    hρUinj fun g => ?_
  · rw [← map_pow, hxk, map_one]
  · rw [eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    have hv' : (v : W) ∈ U ⊓ LinearMap.ker (ρ x - 1) := by
      refine Submodule.mem_inf.2 ⟨v.2, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact congrArg Subtype.val hv
    rw [hUfix, Submodule.mem_bot] at hv'
    exact (Submodule.mem_bot K).2 (Subtype.ext hv')
  · rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hxg g]

theorem orderOf_eq_six_of_sq_sub_add_one {R : Type*} [CommRing R] {x : R}
    (h0 : x ^ 2 - x + 1 = 0) (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) : orderOf x = 6 := by
  have hx3 : x ^ 3 = -1 := by linear_combination (x + 1) * h0
  have hx6 : x ^ 6 = 1 := by linear_combination (x ^ 3 - 1) * hx3
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) hx6 fun r hr hr6 => ?_
  have hr' : r = 2 ∨ r = 3 := by
    rcases (Nat.Prime.dvd_mul hr).1 (show r ∣ 2 * 3 from hr6) with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)
  rcases hr' with rfl | rfl
  · intro h
    exact h2 (by linear_combination hx3 - h)
  · intro h
    have hx1 : x = -1 := by linear_combination hx3 - x * h
    exact h3 (by linear_combination h0 - (x - 2) * hx1)

theorem orderOf_eq_six {q p : ℕ} (hp : p.Prime) (hq : 3 ∣ q) (hpq : p ∣ q ^ 2 - q + 1) :
    orderOf (q : ZMod p) = 6 := by
  have h0 : (q : ZMod p) ^ 2 - q + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 hpq
    rwa [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero q), Nat.cast_pow,
      Nat.cast_one] at this
  refine orderOf_eq_six_of_sq_sub_add_one h0 (fun h2 => ?_) (fun h3 => ?_)
  · have h2' : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h2)
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2'
    revert h0
    generalize (q : ZMod 2) = y
    revert y
    decide
  · have h3' : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast h3)
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3'
    rw [(ZMod.natCast_eq_zero_iff q 3).2 hq] at h0
    revert h0
    decide

end CFSG.Walter.Ree.Cyclic
