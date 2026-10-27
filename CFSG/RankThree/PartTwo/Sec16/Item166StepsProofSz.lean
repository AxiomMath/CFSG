module

public import CFSG.LieType.Ree.SuzukiBorelStructure
import CFSG.LieType.Steinberg.CentralExt.SuzukiMultiplier

public section

namespace CFSG.RankThree.PartTwo.Sec16.Steps166

open CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiSElt_zero_mul_zero (hK : Nat.card K = 2 ^ (2 * a + 1))
    (v w : K) : suzukiSElt a K 0 v * suzukiSElt a K 0 w = suzukiSElt a K 0 (v + w) := by
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [suzukiSElt_mul hK]
  congr 1 <;> simp [zero_pow hθ0]

theorem suzukiZ0_comm (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : suzukiGroup a K} (hx : x ∈ suzukiZ0 a K) (hy : y ∈ suzukiZ0 a K) : x * y = y * x := by
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).mp hx
  obtain ⟨w, rfl⟩ := (mem_suzukiZ0_iff hK).mp hy
  rw [suzukiSElt_zero_mul_zero hK, suzukiSElt_zero_mul_zero hK, add_comm]

theorem suzukiZ0_sq (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : suzukiGroup a K} (hx : x ∈ suzukiZ0 a K) : x ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).mp hx
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  rw [sq, suzukiSElt_zero_mul_zero hK, ← suzukiSElt_zero_zero hK]
  exact congrArg (suzukiSElt a K 0) (by linear_combination v * h2)

theorem suzukiZ0_ne_bot (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiZ0 a K ≠ ⊥ := by
  intro h
  have hmem : suzukiSElt a K 0 1 ∈ suzukiZ0 a K := (mem_suzukiZ0_iff hK).mpr ⟨1, rfl⟩
  rw [h, Subgroup.mem_bot, ← suzukiSElt_zero_zero hK, suzukiSElt_inj] at hmem
  exact one_ne_zero hmem.2

@[expose] noncomputable def suzukiDHom166 : Kˣ →* suzukiGroup a K :=
  MonoidHom.mk' (suzukiDElt a K) fun l m => (suzukiDElt_mul l m).symm

theorem two_pow_odd_sub_one_mod_three (a : ℕ) : (2 ^ (2 * a + 1) - 1) % 3 = 1 := by
  have h : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  omega

theorem two_pow_odd_sub_one_mod_two (a : ℕ) : (2 ^ (2 * a + 1) - 1) % 2 = 1 := by
  have h : 2 ^ (2 * a + 1) % 2 = 0 := by
    rw [pow_succ, Nat.mul_mod_left]
  have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  omega

theorem exists_frobenius_pair (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ t : suzukiGroup a K, t ^ p = 1 ∧
      t ∈ Subgroup.normalizer (suzukiZ0 a K : Set (suzukiGroup a K)) ∧
      ∀ x ∈ suzukiZ0 a K, t * x * t⁻¹ = x → x = 1 := by
  set N := 2 ^ (2 * a + 1) - 1 with hN
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN1 : N ≠ 1 := by omega
  set p := N.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime hN1
  have hpN : p ∣ N := Nat.minFac_dvd N
  have hp2 : p ≠ 2 := by
    rintro h2
    rw [h2] at hpN
    have := two_pow_odd_sub_one_mod_two a
    omega
  have hp3 : p ≠ 3 := by
    rintro h3
    rw [h3] at hpN
    have := two_pow_odd_sub_one_mod_three a
    omega
  have hp3' : 3 < p := by
    have := hpp.two_le
    omega
  refine ⟨p, hpp, hp3', ?_⟩
  have : Fact p.Prime := ⟨hpp⟩
  have hcardU : Nat.card Kˣ = N := by rw [Nat.card_units, hK]
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' p (hcardU ▸ hpN)
  refine ⟨suzukiDHom166 (a := a) l⁻¹, ?_, ?_, ?_⟩
  · rw [← map_pow, inv_pow, ← hl, pow_orderOf_eq_one, inv_one, map_one]
  ·
    have ht : suzukiDHom166 (a := a) l⁻¹ = (suzukiDElt a K l)⁻¹ := by
      change suzukiDElt a K l⁻¹ = _
      rw [suzukiDElt_inv]
    rw [ht]
    refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).mp hx
      rw [inv_inv, suzukiDElt_conj hK, mul_zero]
      exact (mem_suzukiZ0_iff hK).mpr ⟨_, rfl⟩
    · intro hx
      rw [inv_inv] at hx
      obtain ⟨v, hv⟩ := (mem_suzukiZ0_iff hK).mp hx
      have hx' : x = suzukiDElt a K l * suzukiSElt a K 0 v * (suzukiDElt a K l)⁻¹ := by
        rw [hv]
        group
      rw [hx', suzukiDElt_conj' hK, mul_zero]
      exact (mem_suzukiZ0_iff hK).mpr ⟨_, rfl⟩
  · intro x hx hfix
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).mp hx
    have ht : suzukiDHom166 (a := a) l⁻¹ = (suzukiDElt a K l)⁻¹ := by
      change suzukiDElt a K l⁻¹ = _
      rw [suzukiDElt_inv]
    rw [ht, inv_inv, suzukiDElt_conj hK, mul_zero, suzukiSElt_inj] at hfix
    have hv : ((l : K) ^ (2 ^ (a + 1) + 1) - 1) * v = 0 := by
      rw [sub_mul, one_mul, hfix.2, sub_self]
    rcases mul_eq_zero.mp hv with h | h
    · exfalso
      have hl1 : l ^ (2 ^ (a + 1) + 1) = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact sub_eq_zero.mp h
      have hdvd : p ∣ 2 ^ (a + 1) + 1 := hl ▸ orderOf_dvd_of_pow_eq_one hl1
      have hcop := CFSG.LieType.Steinberg.CentralExt.SuzukiClosed.coprime_tits a
      rw [add_comm 1] at hcop
      exact hpp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left hpN hcop).eq_one_of_dvd hdvd)
    · rw [h]
      exact suzukiSElt_zero_zero hK

end CFSG.RankThree.PartTwo.Sec16.Steps166
