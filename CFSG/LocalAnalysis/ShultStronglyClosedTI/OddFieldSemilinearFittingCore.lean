module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAbelianNormalizer
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.ShultStronglyClosedTI.MiscAlgebra

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

theorem exists_prime_dvd_pow_sub_one_not_dvd {r q₀ : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hq₀ : 2 ≤ q₀) : ∃ s, s.Prime ∧ s ∣ q₀ ^ r - 1 ∧ ¬ s ∣ q₀ - 1 := by
  by_contra! h
  have : Fact r.Prime := ⟨hr⟩
  have hr2' := hr.two_le
  obtain ⟨L, hL⟩ : ∃ L, L = ∑ i ∈ Finset.range r, q₀ ^ i := ⟨_, rfl⟩
  have hmul : L * (q₀ - 1) = q₀ ^ r - 1 := hL ▸ geom_sum_mul_of_one_le (by omega) r
  have hq1 : q₀ - 1 ≠ 0 := by omega
  have hrL : r < L := by
    rw [hL]
    calc r = ∑ _i ∈ Finset.range r, 1 := by simp
      _ < ∑ i ∈ Finset.range r, q₀ ^ i :=
        Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ (by omega))
          ⟨1, Finset.mem_range.mpr hr.one_lt, by rw [pow_one]; omega⟩
  have hL0 : L ≠ 0 := by omega
  have hprime : ∀ {s : ℕ}, s.Prime → s ∣ L → s = r := by
    intro s hs hsL
    have hs1 : s ∣ q₀ - 1 := h s hs (hmul ▸ dvd_mul_of_dvd_left hsL _)
    have hq : (q₀ : ZMod s) = 1 := by
      have h0 := (ZMod.natCast_eq_zero_iff (q₀ - 1) s).mpr hs1
      rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_eq_zero] at h0
    have hLs : (L : ZMod s) = r := by
      simp [hL, hq]
    have hr0 : (r : ZMod s) = 0 := by
      rw [← hLs]
      exact (ZMod.natCast_eq_zero_iff L s).mpr hsL
    exact (Nat.prime_dvd_prime_iff_eq hs hr).mp ((ZMod.natCast_eq_zero_iff r s).mp hr0)
  have hLeq := Nat.eq_prime_pow_of_unique_prime_dvd hL0 hprime
  obtain ⟨s, hs, hsL⟩ := Nat.exists_prime_and_dvd (show L ≠ 1 by omega)
  have hrL' : r ∣ L := hprime hs hsL ▸ hsL
  have hr1 : r ∣ q₀ - 1 := h r hr (hmul ▸ dvd_mul_of_dvd_left hrL' _)
  have hrq : ¬ r ∣ q₀ := fun hrq => hr.one_lt.ne' (Nat.dvd_one.mp (by
    have h' := Nat.dvd_sub hrq hr1
    rwa [Nat.sub_sub_self (by omega)] at h'))
  have hlte := padicValNat.pow_sub_pow (hr.odd_of_ne_two hr2) (show 1 < q₀ by omega) hr1 hrq
    hr.ne_zero
  rw [one_pow, ← hmul, padicValNat.mul hL0 hq1, padicValNat_self] at hlte
  have hv : padicValNat r L = 1 := by omega
  rw [hLeq, padicValNat.prime_pow] at hv
  rw [hLeq, hv, pow_one] at hrL
  exact lt_irrefl _ hrL

theorem exists_units_iterate_ne_one {K : Type*} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ e) {τ : RingAut K} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hτ : orderOf τ = r) :
    ∃ d : Kˣ, ∀ n : ℕ, (fun z : Kˣ => z * (ringAutUnits K τ z)⁻¹)^[n] d ≠ 1 := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · rw [pow_zero] at hK
      exact absurd hK (Finite.one_lt_card (α := K)).ne'
    · exact he
  obtain ⟨-, -, -, -, -, hsub⟩ := finite_field_automorphism_fixed_field_cardinality hp he hK
  obtain ⟨hdvd, S, hS, hScard⟩ := hsub (Subgroup.zpowers τ)
  rw [Nat.card_zpowers, hτ] at hdvd hScard
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, q₀ = p ^ (e / r) := ⟨_, rfl⟩
  rw [← hq₀] at hScard
  have hq₀2 : 2 ≤ q₀ := by
    rw [hq₀]
    calc 2 ≤ p ^ 1 := by rw [pow_one]; exact hp.two_le
      _ ≤ p ^ (e / r) := Nat.pow_le_pow_right hp.pos (Nat.div_pos (Nat.le_of_dvd he hdvd) hr.pos)
  have hKu : Nat.card Kˣ = q₀ ^ r - 1 := by
    rw [Nat.card_units, hK, hq₀, ← pow_mul, Nat.div_mul_cancel hdvd]
  obtain ⟨s, hs, hsdvd, hsnot⟩ := exists_prime_dvd_pow_sub_one_not_dvd hr hr2 hq₀2
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' s (hKu ▸ hsdvd)
  have hfixed : ∀ z : Kˣ, ringAutUnits K τ z = z → z ^ (q₀ - 1) = 1 := by
    intro z hz
    have hzS : (z : K) ∈ S := by
      rw [← SetLike.mem_coe, hS]
      intro τ' hτ'
      have hstab : Subgroup.zpowers τ ≤ MulAction.stabilizer (RingAut K) (z : K) :=
        Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (congrArg Units.val hz))
      exact MulAction.mem_stabilizer_iff.mp (hstab hτ')
    have : Fintype S := Fintype.ofFinite S
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨z, hzS⟩ : S)
      (fun h0 => z.ne_zero (congrArg Subtype.val h0))
    rw [Fintype.card_eq_nat_card, hScard] at h1
    exact Units.ext (congrArg Subtype.val h1)
  let ψ : Kˣ →* Kˣ := MonoidHom.mk' (fun z => z * (ringAutUnits K τ z)⁻¹) fun a b => by
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  have hψ : (⇑ψ) = fun z : Kˣ => z * (ringAutUnits K τ z)⁻¹ := rfl
  have hstep : ∀ z : Kˣ, orderOf z = s → orderOf (ψ z) = s := by
    intro z hz
    apply orderOf_eq_prime
    · rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
    · intro h1
      apply hsnot
      rw [← hz]
      exact orderOf_dvd_of_pow_eq_one (hfixed z (mul_inv_eq_one.mp h1).symm)
  have hiter : ∀ n : ℕ, orderOf (ψ^[n] d) = s := by
    intro n
    induction n with
    | zero => exact hd
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ ih
  refine ⟨d, fun n h1 => hs.one_lt.ne' ?_⟩
  rw [← hψ] at h1
  rw [← hiter n, h1, orderOf_one]

theorem fittingSubgroup_eq_range_of_conj_ringAut {K : Type*} [Field K] [Finite K] {p e : ℕ}
    (hp : p.Prime) (he : Odd e) (hK : Nat.card K = p ^ e) {A : Type*} [Group A] [Finite A]
    (ι : Kˣ →* A) (hι : Function.Injective ι)
    (hconj : ∀ a : A, ∃ σ : RingAut K, ∀ d : Kˣ, a * ι d * a⁻¹ = ι (ringAutUnits K σ d))
    (hcent : ∀ a : A, (∀ d : Kˣ, a * ι d = ι d * a) → a ∈ ι.range) :
    fittingSubgroup A = ι.range ∧ Subgroup.centralizer (ι.range : Set A) = ι.range := by
  have hnormal : ι.range.Normal := ⟨fun n hn a => by
    obtain ⟨d, rfl⟩ := hn
    obtain ⟨σ, hσ⟩ := hconj a
    exact ⟨_, (hσ d).symm⟩⟩
  have hnil : Group.IsNilpotent ι.range := Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hι)
  have hle : ι.range ≤ fittingSubgroup A :=
    le_sSup (s := {N : Subgroup A | N.Normal ∧ Group.IsNilpotent N}) ⟨hnormal, hnil⟩
  have hcentr : Subgroup.centralizer (ι.range : Set A) = ι.range := by
    apply le_antisymm
    · intro a ha
      exact hcent a fun d => (Subgroup.mem_centralizer_iff.mp ha (ι d) ⟨d, rfl⟩).symm
    · rintro _ ⟨d, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      obtain ⟨d', rfl⟩ := hh
      rw [← map_mul, ← map_mul, mul_comm]
  refine ⟨le_antisymm (fun y hy => ?_) hle, hcentr⟩
  by_contra hyX
  obtain ⟨σ, hσ⟩ := hconj y
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality hp he.pos hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact he.pos.ne')
  have hσ1 : orderOf σ ≠ 1 := by
    intro h1
    rw [orderOf_eq_one_iff] at h1
    subst h1
    refine hyX (hcent y fun d => ?_)
    have h := hσ d
    rw [map_one, MulAut.one_apply] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  obtain ⟨r, hr, hrσ⟩ := Nat.exists_prime_and_dvd hσ1
  have hre : r ∣ e := hrσ.trans (hcard ▸ orderOf_dvd_natCard σ)
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr he (even_iff_two_dvd.mpr hre)
  obtain ⟨m, hm⟩ : ∃ m, m = orderOf σ / r := ⟨_, rfl⟩
  have hτ : orderOf (σ ^ m) = r := hm ▸ orderOf_pow_orderOf_div (orderOf_pos σ).ne' hrσ
  have hpow : ∀ (n : ℕ) (d : Kˣ), y ^ n * ι d * (y ^ n)⁻¹ = ι (ringAutUnits K (σ ^ n) d) := by
    intro n
    induction n with
    | zero => intro d; simp
    | succ n ih =>
      intro d
      rw [pow_succ' y, pow_succ' σ, map_mul, MulAut.mul_apply, ← hσ, ← ih]
      group
  have hy : y ^ m ∈ fittingSubgroup A := Subgroup.pow_mem _ hy m
  have hcomm : ∀ z : Kˣ, ⁅ι z, y ^ m⁆ = ι (z * (ringAutUnits K (σ ^ m) z)⁻¹) := by
    intro z
    rw [commutatorElement_def, map_mul, ← map_inv (ringAutUnits K (σ ^ m)) z, ← hpow m z⁻¹,
      map_inv ι]
    group
  obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries _).mp
    (inferInstance : Group.IsNilpotent (fittingSubgroup A))
  have hmem : ∀ (n : ℕ) (z : Kˣ),
      ι ((fun z : Kˣ => z * (ringAutUnits K (σ ^ m) z)⁻¹)^[n] z) ∈
        (fittingSubgroup A).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => intro z; exact hle ⟨z, rfl⟩
    | succ n ih =>
      intro z
      have h := Subgroup.commutator_mem_commutator (ih z) hy
      rw [hcomm] at h
      rw [Function.iterate_succ_apply']
      exact h
  obtain ⟨d, hd⟩ := exists_units_iterate_ne_one hp hK hr hr2 hτ
  apply hd c
  apply hι
  rw [map_one, ← Subgroup.mem_bot, ← hc]
  exact hmem c d

end CFSG.ShultStronglyClosedTI.MiscAlgebra
