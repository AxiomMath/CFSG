module

import Mathlib.NumberTheory.Multiplicity
import CFSG.Walter.PSL2Facts.FieldAut
public import CFSG.Walter.Bender1970.S2.Basic
public import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

theorem mul_sq_le_pow {q₀ r : ℕ} (hq₀ : 5 ≤ q₀) (hr : 3 ≤ r) : r * (q₀ + 1) ^ 2 ≤ q₀ ^ r := by
  induction r, hr using Nat.le_induction with
  | base => nlinarith [Nat.mul_le_mul hq₀ hq₀]
  | succ r hr ih =>
    have h1 : r + 1 ≤ q₀ * r := by nlinarith
    calc (r + 1) * (q₀ + 1) ^ 2 ≤ (q₀ * r) * (q₀ + 1) ^ 2 := Nat.mul_le_mul_right _ h1
      _ = q₀ * (r * (q₀ + 1) ^ 2) := by ring
      _ ≤ q₀ * q₀ ^ r := Nat.mul_le_mul_left _ ih
      _ = q₀ ^ (r + 1) := by ring

theorem lt_ordCompl_pow_sub_one {q₀ r : ℕ} (hq₀ : 3 ≤ q₀) (hodd : Odd q₀) (hr : r.Prime)
    (hr2 : r ≠ 2) : q₀ - 1 < ordCompl[r] (q₀ ^ r - 1) := by
  have : Fact r.Prime := ⟨hr⟩
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hlt : q₀ < q₀ ^ r := by
    calc q₀ = q₀ ^ 1 := (pow_one q₀).symm
      _ < q₀ ^ r := Nat.pow_lt_pow_right (by omega) (by omega)
  by_cases hdvd : r ∣ q₀ - 1
  · have hrq : ¬ r ∣ q₀ := by
      intro h
      have h1 : r ∣ q₀ - (q₀ - 1) := Nat.dvd_sub h hdvd
      rw [show q₀ - (q₀ - 1) = 1 by omega] at h1
      exact hr.one_lt.ne' (Nat.dvd_one.mp h1)
    have hv : padicValNat r (q₀ ^ r - 1 ^ r) = padicValNat r (q₀ - 1) + padicValNat r r :=
      padicValNat.pow_sub_pow hrodd (by omega : 1 < q₀) hdvd hrq hr.ne_zero
    rw [one_pow, padicValNat_self] at hv
    have hproj : ordProj[r] (q₀ ^ r - 1) = r * ordProj[r] (q₀ - 1) := by
      rw [Nat.factorization_def _ hr, Nat.factorization_def _ hr, hv, pow_succ, mul_comm]
    have hproj_le : ordProj[r] (q₀ - 1) ≤ q₀ - 1 := Nat.ordProj_le r (by omega)
    have hNeq := Nat.ordProj_mul_ordCompl_eq_self (q₀ ^ r - 1) r
    have hq₀5 : 5 ≤ q₀ := by
      obtain ⟨k, hk⟩ := hdvd
      have h2 : 2 ∣ q₀ - 1 := by
        rcases hodd with ⟨j, hj⟩
        exact ⟨j, by omega⟩
      have hk2 : 2 ∣ k := by
        rw [hk] at h2
        exact (Nat.Coprime.dvd_mul_left (Nat.coprime_two_left.mpr hrodd)).mp h2
      rcases hk2 with ⟨j, rfl⟩
      have hj : j ≠ 0 := by
        rintro rfl
        omega
      have : r * (2 * j) ≥ 6 := by nlinarith [Nat.one_le_iff_ne_zero.mpr hj]
      omega
    have hbig := mul_sq_le_pow hq₀5 hr3
    by_contra hle
    push Not at hle
    have h1 : q₀ ^ r - 1 ≤ r * (q₀ - 1) * (q₀ - 1) := by
      calc q₀ ^ r - 1 = ordProj[r] (q₀ ^ r - 1) * ordCompl[r] (q₀ ^ r - 1) := hNeq.symm
        _ ≤ (r * (q₀ - 1)) * (q₀ - 1) :=
          Nat.mul_le_mul (by rw [hproj]; exact Nat.mul_le_mul_left _ hproj_le) hle
    obtain ⟨a, rfl⟩ : ∃ a, q₀ = a + 1 := ⟨q₀ - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h1
    have h2 : r * a * a + 4 * r * (a + 1) = r * (a + 1 + 1) ^ 2 := by ring
    have h3 : 2 ≤ 4 * r * (a + 1) := by nlinarith
    omega
  · have hnd : ¬ r ∣ q₀ ^ r - 1 := by
      intro h
      apply hdvd
      have h1 : ((q₀ ^ r - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, ZMod.pow_card,
        Nat.cast_one] at h1
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega), Nat.cast_one]
      exact h1
    have hcompl : ordCompl[r] (q₀ ^ r - 1) = q₀ ^ r - 1 := by
      rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero, Nat.div_one]
    rw [hcompl]
    omega

theorem lt_ordCompl_pow_add_one {q₀ r : ℕ} (hq₀ : 3 ≤ q₀) (hodd : Odd q₀) (hr : r.Prime)
    (hr2 : r ≠ 2) : q₀ + 1 < ordCompl[r] (q₀ ^ r + 1) := by
  have : Fact r.Prime := ⟨hr⟩
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hlt : q₀ < q₀ ^ r := by
    calc q₀ = q₀ ^ 1 := (pow_one q₀).symm
      _ < q₀ ^ r := Nat.pow_lt_pow_right (by omega) (by omega)
  by_cases hdvd : r ∣ q₀ + 1
  · have hrq : ¬ r ∣ q₀ := by
      intro h
      have h1 : r ∣ q₀ + 1 - q₀ := Nat.dvd_sub hdvd h
      rw [show q₀ + 1 - q₀ = 1 by omega] at h1
      exact hr.one_lt.ne' (Nat.dvd_one.mp h1)
    have hv : padicValNat r (q₀ ^ r + 1 ^ r) = padicValNat r (q₀ + 1) + padicValNat r r :=
      padicValNat.pow_add_pow hrodd hdvd hrq hrodd
    rw [one_pow, padicValNat_self] at hv
    have hproj : ordProj[r] (q₀ ^ r + 1) = r * ordProj[r] (q₀ + 1) := by
      rw [Nat.factorization_def _ hr, Nat.factorization_def _ hr, hv, pow_succ, mul_comm]
    have hproj_le : ordProj[r] (q₀ + 1) ≤ q₀ + 1 := Nat.ordProj_le r (by omega)
    have hNeq := Nat.ordProj_mul_ordCompl_eq_self (q₀ ^ r + 1) r
    have hq₀5 : 5 ≤ q₀ := by
      obtain ⟨k, hk⟩ := hdvd
      have h2 : 2 ∣ q₀ + 1 := by
        rcases hodd with ⟨j, hj⟩
        exact ⟨j + 1, by omega⟩
      have hk2 : 2 ∣ k := by
        rw [hk] at h2
        exact (Nat.Coprime.dvd_mul_left (Nat.coprime_two_left.mpr hrodd)).mp h2
      rcases hk2 with ⟨j, rfl⟩
      have hj : j ≠ 0 := by
        rintro rfl
        omega
      have : r * (2 * j) ≥ 6 := by nlinarith [Nat.one_le_iff_ne_zero.mpr hj]
      omega
    have hbig := mul_sq_le_pow hq₀5 hr3
    by_contra hle
    push Not at hle
    have h1 : q₀ ^ r + 1 ≤ r * (q₀ + 1) * (q₀ + 1) := by
      calc q₀ ^ r + 1 = ordProj[r] (q₀ ^ r + 1) * ordCompl[r] (q₀ ^ r + 1) := hNeq.symm
        _ ≤ (r * (q₀ + 1)) * (q₀ + 1) :=
          Nat.mul_le_mul (by rw [hproj]; exact Nat.mul_le_mul_left _ hproj_le) hle
    have h4 : r * (q₀ + 1) * (q₀ + 1) = r * (q₀ + 1) ^ 2 := by ring
    omega
  · have hnd : ¬ r ∣ q₀ ^ r + 1 := by
      intro h
      apply hdvd
      have h1 : ((q₀ ^ r + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [Nat.cast_add, Nat.cast_pow, ZMod.pow_card, Nat.cast_one] at h1
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
      exact h1
    have hcompl : ordCompl[r] (q₀ ^ r + 1) = q₀ ^ r + 1 := by
      rw [Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero, Nat.div_one]
    rw [hcompl]
    omega

theorem mem_zpowers_r_one_of_orderOf_ne_two {n : ℕ} {x : DihedralGroup n}
    (hx : orderOf x ≠ 2) : x ∈ Subgroup.zpowers (DihedralGroup.r 1) := by
  rcases x with i | i
  · obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
    exact ⟨k, DihedralGroup.r_one_zpow k⟩
  · exact absurd (DihedralGroup.orderOf_sr i) hx

theorem psl2_odd_false_of_mulAut
    {p f r : ℕ} [Fact p.Prime] (hp : Odd p) (hf : 0 < f)
    (h5 : 5 ≤ p ^ f) (h8 : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) (hr : r.Prime) (hr2 : r ≠ 2)
    (α : MulAut PSL(2, GaloisField p f)) (hα : orderOf α = r)
    (S : Sylow 2 PSL(2, GaloisField p f))
    (hαS : ∀ x ∈ (S : Subgroup PSL(2, GaloisField p f)), α x = x)
    {ℓ : PSL(2, GaloisField p f)} (hℓS : ℓ ∈ (S : Subgroup PSL(2, GaloisField p f)))
    (hℓ : orderOf ℓ = 2)
    (hαD : ∀ x ∈ Subgroup.centralizer ({ℓ} : Set PSL(2, GaloisField p f)),
      Nat.Coprime (orderOf (x⁻¹ * α x)) r → α x = x) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hrf, ⟨eα⟩⟩ := psl2_mulAut_of_centralizes_sylow_two hp hf h5 h8 hr hr2 α hα S hαS
  have hf' : 0 < f / r := Nat.div_pos (Nat.le_of_dvd hf hrf) hr.pos
  have hpow : p ^ f = (p ^ (f / r)) ^ r := by rw [← pow_mul, Nat.div_mul_cancel hrf]
  set q₀ := p ^ (f / r) with hq₀
  have hq₀odd : Odd q₀ := hp.pow
  have hq₀3 : 3 ≤ q₀ := by
    have h1 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      rcases hp with ⟨k, hk⟩
      omega
    calc 3 ≤ p := h1
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (f / r) := Nat.pow_le_pow_right (by omega) hf'
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hmod : p ^ f % 8 = q₀ % 8 := by rw [hpow]; exact pow_mod_eight_of_odd hq₀odd hrodd
  have hq27 : 27 ≤ p ^ f := by
    rw [hpow]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q₀ ^ 3 := Nat.pow_le_pow_left hq₀3 3
      _ ≤ q₀ ^ r := Nat.pow_le_pow_right (by omega) hr3
  set D := Subgroup.centralizer ({ℓ} : Set PSL(2, GaloisField p f)) with hD
  set E := α.toMonoidHom.eqLocus (MonoidHom.id PSL(2, GaloisField p f)) with hE
  have hℓE : ℓ ∈ E := hαS ℓ hℓS
  set ℓE : E := ⟨ℓ, hℓE⟩ with hℓEdef
  have hℓE2 : orderOf (eα ℓE) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hℓ]
  have hDEmap : (Subgroup.centralizer ({ℓE} : Set E)).map E.subtype = D ⊓ E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, y.2⟩
      show (y : PSL(2, GaloisField p f)) ∈ D
      have hy' : y ∈ Subgroup.centralizer ({ℓE} : Set E) := hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hy'
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hy')
    · rintro ⟨hxD, hxE⟩
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      have hxD' : x ∈ D := hxD
      rw [Subgroup.mem_centralizer_singleton_iff] at hxD'
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hxD')
  have hDEcard : Nat.card (D ⊓ E : Subgroup PSL(2, GaloisField p f)) =
      Nat.card (Subgroup.centralizer ({eα ℓE} : Set PSL(2, GaloisField p (f / r)))) := by
    rw [← hDEmap, Subgroup.card_map_of_injective E.subtype_injective,
      ← map_centralizer_singleton_mulEquiv eα, Subgroup.card_map_of_injective eα.injective]
  obtain ⟨n, m, ⟨d⟩, hDn, hDEm, hNT⟩ : ∃ n m : ℕ, Nonempty (D ≃* DihedralGroup n) ∧
      Nat.card D = 2 * n ∧ Nat.card (D ⊓ E : Subgroup PSL(2, GaloisField p f)) = m ∧
        m < ordCompl[r] (2 * n) := by
    have hD1 := psl2_odd_centralizer_involution hp hf hℓ
    have hE1 := psl2_odd_centralizer_involution hp hf' hℓE2
    have hq : q₀ % 4 = 1 ∨ q₀ % 4 = 3 := by
      have := Nat.odd_iff.mp hq₀odd
      omega
    rcases hq with hq | hq
    · have hq' : p ^ f % 4 = 1 := by omega
      obtain ⟨hDc, hDd⟩ := hD1.1 hq'
      obtain ⟨hEc, -⟩ := hE1.1 hq
      refine ⟨(p ^ f - 1) / 2, q₀ - 1, hDd, ?_, by rw [hDEcard, hEc], ?_⟩
      · rw [hDc]
        omega
      · rw [show 2 * ((p ^ f - 1) / 2) = q₀ ^ r - 1 by rw [← hpow]; omega]
        exact lt_ordCompl_pow_sub_one hq₀3 hq₀odd hr hr2
    · have hq' : p ^ f % 4 = 3 := by omega
      obtain ⟨hDc, hDd⟩ := hD1.2 hq'
      obtain ⟨hEc, -⟩ := hE1.2 hq
      refine ⟨(p ^ f + 1) / 2, q₀ + 1, hDd, ?_, by rw [hDEcard, hEc], ?_⟩
      · rw [hDc]
        omega
      · rw [show 2 * ((p ^ f + 1) / 2) = q₀ ^ r + 1 by rw [← hpow]; omega]
        exact lt_ordCompl_pow_add_one hq₀3 hq₀odd hr hr2
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, mul_zero] at hDn
    exact (Nat.card_pos (α := D)).ne' hDn
  set g₀ : PSL(2, GaloisField p f) :=
    ((d.symm (DihedralGroup.r 1) : D) : PSL(2, GaloisField p f)) with hg₀
  have hg₀D : g₀ ∈ D := (d.symm (DihedralGroup.r 1)).2
  have hg₀ord : orderOf g₀ = n := by
    rw [hg₀, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  have hrot : ∀ x ∈ D, orderOf x ≠ 2 → x ∈ Subgroup.zpowers g₀ := by
    intro x hx hx2
    have h1 : d ⟨x, hx⟩ ∈ Subgroup.zpowers (DihedralGroup.r 1) := by
      apply mem_zpowers_r_one_of_orderOf_ne_two
      rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h2 : d.symm (DihedralGroup.r 1 ^ k) = ⟨x, hx⟩ := by
      rw [hk, MulEquiv.symm_apply_apply]
    rw [map_zpow] at h2
    rw [hg₀, ← Subgroup.coe_zpow, h2]
  have hαD' : ∀ x ∈ D, α x ∈ D := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    rw [← hαS ℓ hℓS, ← map_mul, ← map_mul, hx]
  have hn3 : 3 ≤ n := by
    have : 26 ≤ 2 * n := by
      rw [← hDn]
      have hD1 := psl2_odd_centralizer_involution hp hf hℓ
      have hq : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
        have := Nat.odd_iff.mp (hp.pow (n := f))
        omega
      rcases hq with hq | hq
      · rw [(hD1.1 hq).1]
        omega
      · rw [(hD1.2 hq).1]
        omega
    omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, g₀ ^ k = α g₀ := by
    apply Subgroup.mem_zpowers_iff.mp
    apply hrot _ (hαD' g₀ hg₀D)
    rw [MulEquiv.orderOf_eq, hg₀ord]
    omega
  set h₀ := g₀ ^ (ordProj[r] n) with hh₀
  have hh₀ord : orderOf h₀ = ordCompl[r] n := by
    rw [hh₀, orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero) (hg₀ord ▸ Nat.ordProj_dvd n r),
      hg₀ord]
  have hαh₀ : α h₀ = h₀ ^ k := by
    rw [hh₀, map_pow, ← hk, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hfix : Subgroup.zpowers h₀ ≤ D ⊓ E := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hxD : h₀ ^ j ∈ D :=
      D.zpow_mem (D.pow_mem hg₀D _) j
    refine ⟨hxD, ?_⟩
    apply hαD _ hxD
    have hmem : (h₀ ^ j)⁻¹ * α (h₀ ^ j) ∈ Subgroup.zpowers h₀ := by
      rw [map_zpow, hαh₀, ← zpow_mul]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers h₀ j))
        (Subgroup.zpow_mem_zpowers h₀ (k * j))
    have h1 := orderOf_dvd_of_mem_zpowers hmem
    rw [hh₀ord] at h1
    exact Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_ordCompl hr hn0).symm
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
  have hS4 := psl2_sylow_two_isKleinFour (GaloisField p f) hK hp hf h8 S
  have hSD : (S : Subgroup PSL(2, GaloisField p f)) ≤ D ⊓ E := by
    intro x hx
    refine ⟨?_, hαS x hx⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have := hS4.isMulCommutative
    exact congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨ℓ, hℓS⟩)
  have hSnot : ¬ (S : Subgroup PSL(2, GaloisField p f)) ≤ Subgroup.zpowers h₀ := by
    intro h
    have : IsCyclic ((S : Subgroup PSL(2, GaloisField p f)).subgroupOf (Subgroup.zpowers h₀)) :=
      Subgroup.isCyclic _
    have : IsCyclic (S : Subgroup PSL(2, GaloisField p f)) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
        (MulEquiv.surjective _)
    exact hS4.not_isCyclic this
  have hdvd :
      Nat.card (Subgroup.zpowers h₀) ∣ Nat.card (D ⊓ E : Subgroup PSL(2, GaloisField p f)) :=
    Subgroup.card_dvd_of_le hfix
  rw [Nat.card_zpowers, hh₀ord, hDEm] at hdvd
  have hne : ordCompl[r] n ≠ m := by
    intro h
    apply hSnot
    have h1 : Subgroup.zpowers h₀ = D ⊓ E := Subgroup.eq_of_le_of_card_ge hfix (by
      rw [hDEm, Nat.card_zpowers, hh₀ord, h])
    rw [h1]
    exact hSD
  have hm0 : 0 < m := by
    rw [← hDEm]
    exact Nat.card_pos
  have h2n : ordCompl[r] (2 * n) = 2 * ordCompl[r] n := by
    rw [Nat.ordCompl_mul]
    congr 1
    rw [Nat.factorization_eq_zero_of_not_dvd (fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega), pow_zero, Nat.div_one]
  obtain ⟨c, hc⟩ := hdvd
  rw [h2n] at hNT
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  nlinarith

theorem IsTypeL2Odd.false_of_mulAut
    {L : Type*} [Group L] [Finite L] (hL : IsTypeL2Odd L)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (α : MulAut L) (hα : orderOf α = r) (S : Sylow 2 L)
    (hαS : ∀ x ∈ (S : Subgroup L), α x = x) {ℓ : L} (hℓS : ℓ ∈ (S : Subgroup L))
    (hℓ : orderOf ℓ = 2)
    (hαD : ∀ x ∈ Subgroup.centralizer ({ℓ} : Set L),
      Nat.Coprime (orderOf (x⁻¹ * α x)) r → α x = x) : False := by
  obtain ⟨p, f, hp, hpodd, hf, h5, h8, ⟨e⟩⟩ := hL
  have hes : Function.Surjective e.toMonoidHom := e.surjective
  have happ : ∀ y : L, MulAut.congr e α (e y) = e (α y) := by
    intro y
    show e (α (e.symm (e y))) = e (α y)
    rw [MulEquiv.symm_apply_apply]
  refine psl2_odd_false_of_mulAut hpodd hf h5 h8 hr hr2 (MulAut.congr e α)
    (by rwa [MulEquiv.orderOf_eq]) (S.mapSurjective hes) ?_ (ℓ := e ℓ) ?_
    (by rwa [MulEquiv.orderOf_eq]) ?_
  · intro x hx
    rw [Sylow.coe_mapSurjective] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, happ, hαS y hy]
  · rw [Sylow.coe_mapSurjective]
    exact ⟨ℓ, hℓS, rfl⟩
  · intro x hx hcop
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : y ∈ Subgroup.centralizer ({ℓ} : Set L) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      apply e.injective
      rw [map_mul, map_mul]
      exact hx
    have h1 : (e y)⁻¹ * MulAut.congr e α (e y) = e (y⁻¹ * α y) := by
      rw [happ, map_mul, map_inv]
    rw [h1, MulEquiv.orderOf_eq] at hcop
    rw [happ, hαD y hy hcop]

end CFSG.Walter
