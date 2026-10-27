module

public import CFSG.Open.LocalVocabulary

import CFSG.GroupTheory.GroupAction.CoprimeSeriesTrivial

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Open

theorem isUnit_of_trivial {G : Type} [Group G] [Finite G]
    {n : ℕ} {L : Subgroup G} {d₁ d₂ : G} {m : ZMod (2 ^ n - 1)}
    (hn : n ≠ 0) (hcomm : Commute d₁ d₂) (hd₁ : d₁ ^ (2 ^ n - 1) = 1)
    (hd₂ : orderOf d₂ = 2 ^ n - 1)
    (_hLn : d₁ ^ (-m).val * d₂ ∈ normalizer (L : Set G))
    (hOn : d₁ ^ (-m).val * d₂ ∈ normalizer (pCoreOf 2 L : Set G))
    (htriv : ∀ l ∈ L,
      (d₁ ^ (-m).val * d₂) * l * (d₁ ^ (-m).val * d₂)⁻¹ * l⁻¹ ∈ pCoreOf 2 L)
    (hinj : ∀ k : ℕ,
      (∀ l ∈ L, d₂ ^ k * l * (d₂ ^ k)⁻¹ * l⁻¹ ∈ pCoreOf 2 L) → d₂ ^ k = 1) :
    IsUnit m := by
  have hNpos : 0 < 2 ^ n - 1 := by
    have h := Nat.one_lt_two_pow hn
    omega
  haveI : NeZero (2 ^ n - 1) := ⟨hNpos.ne'⟩
  rw [← ZMod.natCast_zmod_val m]
  by_contra hnot
  have hnot' : ¬ Nat.Coprime m.val (2 ^ n - 1) := fun hc =>
    hnot ((ZMod.isUnit_iff_coprime m.val (2 ^ n - 1)).mpr hc)
  have hgcd : Nat.gcd m.val (2 ^ n - 1) ≠ 1 := fun h =>
    hnot' (Nat.coprime_iff_gcd_eq_one.mpr h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpN : p ∣ 2 ^ n - 1 := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hpm : p ∣ m.val := hpdvd.trans (Nat.gcd_dvd_left _ _)
  let e : ℕ := (2 ^ n - 1) / p
  have hpe : p * e = 2 ^ n - 1 := Nat.mul_div_cancel' hpN
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, mul_zero] at hpe
      omega
    · exact h
  have helt : e < 2 ^ n - 1 := by
    rw [← hpe]
    exact lt_mul_of_one_lt_left hepos hp.one_lt
  have hmval : p * (m.val / p) = m.val := Nat.mul_div_cancel' hpm
  have hNmul : 2 ^ n - 1 ∣ e * m.val := by
    refine ⟨m.val / p, ?_⟩
    calc e * m.val = e * (p * (m.val / p)) := by
          conv_lhs => rw [← hmval]
      _ = (p * e) * (m.val / p) := by ring
      _ = (2 ^ n - 1) * (m.val / p) := by rw [hpe]
  have hNcast : ((e * (-m).val : ℕ) : ZMod (2 ^ n - 1)) = 0 := by
    have h1 : ((e * m.val : ℕ) : ZMod (2 ^ n - 1)) = 0 :=
      (ZMod.natCast_eq_zero_iff (e * m.val) (2 ^ n - 1)).mpr hNmul
    calc ((e * (-m).val : ℕ) : ZMod (2 ^ n - 1))
        = (e : ZMod (2 ^ n - 1)) * ((-m).val : ZMod (2 ^ n - 1)) := by
          rw [Nat.cast_mul]
      _ = (e : ZMod (2 ^ n - 1)) * (-m) := by rw [ZMod.natCast_zmod_val]
      _ = -((e : ZMod (2 ^ n - 1)) * m) := by ring
      _ = -(((e * m.val : ℕ) : ZMod (2 ^ n - 1))) := by
          rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      _ = 0 := by rw [h1, neg_zero]
  have hNdvd : 2 ^ n - 1 ∣ e * (-m).val :=
    (ZMod.natCast_eq_zero_iff (e * (-m).val) (2 ^ n - 1)).mp hNcast
  have hpow_d1 : d₁ ^ ((-m).val * e) = 1 := by
    obtain ⟨q, hq⟩ := hNdvd
    rw [mul_comm (-m).val e, hq, pow_mul, hd₁, one_pow]
  have htpow : (d₁ ^ (-m).val * d₂) ^ e = d₂ ^ e := by
    rw [(hcomm.pow_left (-m).val).mul_pow, ← pow_mul, hpow_d1, one_mul]
  have htriv_pow : ∀ l ∈ L,
      (d₁ ^ (-m).val * d₂) ^ e * l * ((d₁ ^ (-m).val * d₂) ^ e)⁻¹ * l⁻¹ ∈
        pCoreOf 2 L := by
    intro l hl
    exact commutator_zpowers_le_of_mem_commutator hOn htriv
      ((d₁ ^ (-m).val * d₂) ^ e)
      (Subgroup.npow_mem_zpowers (d₁ ^ (-m).val * d₂) e) l hl
  have hd₂pow : d₂ ^ e = 1 := by
    apply hinj e
    intro l hl
    rw [← htpow]
    exact htriv_pow l hl
  have hdvd : 2 ^ n - 1 ∣ e := by
    have h := orderOf_dvd_of_pow_eq_one hd₂pow
    rwa [hd₂] at h
  have hle : 2 ^ n - 1 ≤ e := Nat.le_of_dvd hepos hdvd
  omega

theorem conj_eq_of_inv {G : Type} [Group G] {n : ℕ} {d₁ d₂ x : G}
    {m : ZMod (2 ^ n - 1)} (hn : n ≠ 0)
    (hd₁ : d₁ ^ (2 ^ n - 1) = 1) (hinv : x * d₁ * x⁻¹ = d₁⁻¹)
    (hcent : x * (d₁ ^ (-m).val * d₂) * x⁻¹ = d₁ ^ (-m).val * d₂) :
    x * d₂ * x⁻¹ = d₁ ^ (-2 * m).val * d₂ := by
  have hNpos : 0 < 2 ^ n - 1 := by
    have h := Nat.one_lt_two_pow hn
    omega
  haveI : NeZero (2 ^ n - 1) := ⟨hNpos.ne'⟩
  have hconj : x * d₁ ^ (-m).val * x⁻¹ = (d₁ ^ (-m).val)⁻¹ := by
    rw [(conj_pow (a := x) (b := d₁) (i := (-m).val)).symm, hinv, inv_pow]
  have hsplit : x * (d₁ ^ (-m).val * d₂) * x⁻¹ =
      (x * d₁ ^ (-m).val * x⁻¹) * (x * d₂ * x⁻¹) := by group
  rw [hsplit] at hcent
  have hmul : (d₁ ^ (-m).val)⁻¹ * (x * d₂ * x⁻¹) = d₁ ^ (-m).val * d₂ := by
    rwa [hconj] at hcent
  have hx : x * d₂ * x⁻¹ = d₁ ^ (2 * (-m).val) * d₂ := by
    calc x * d₂ * x⁻¹
        = (d₁ ^ (-m).val * (d₁ ^ (-m).val)⁻¹) * (x * d₂ * x⁻¹) := by group
      _ = d₁ ^ (-m).val * ((d₁ ^ (-m).val)⁻¹ * (x * d₂ * x⁻¹)) := by group
      _ = d₁ ^ (-m).val * (d₁ ^ (-m).val * d₂) := by rw [hmul]
      _ = (d₁ ^ (-m).val * d₁ ^ (-m).val) * d₂ := by group
      _ = d₁ ^ ((-m).val + (-m).val) * d₂ := by rw [← pow_add]
      _ = d₁ ^ (2 * (-m).val) * d₂ := by
          rw [show (-m).val + (-m).val = 2 * (-m).val by ring]
  have hcast : ((2 * (-m).val : ℕ) : ZMod (2 ^ n - 1)) =
      (((-2 * m).val : ℕ) : ZMod (2 ^ n - 1)) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  have hmod : 2 * (-m).val ≡ (-2 * m).val [MOD 2 ^ n - 1] :=
    (ZMod.natCast_eq_natCast_iff' (2 * (-m).val) ((-2 * m).val) (2 ^ n - 1)).mp hcast
  have hpow : d₁ ^ (2 * (-m).val) = d₁ ^ (-2 * m).val :=
    (pow_eq_pow_iff_modEq (x := d₁) (n := 2 * (-m).val) (m := (-2 * m).val)).mpr
      (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hd₁) hmod)
  rw [hx, hpow]

end CFSG.Quasithin.Stroth.G5

end
