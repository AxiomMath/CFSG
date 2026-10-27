module

public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.Quasithin.Background.F6CatDickson
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL2OddSylow
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL2OddTools
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL2OddTorus
import CFSG.RankThree.PartTwo.Sec18.Item189StepL16Omega
import CFSG.Walter.PSL2Facts.OddMaximal
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.RankThree.PartTwo.Sec18

open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem eq_top_l2odd189 (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {f : ℕ} (hf : 1 ≤ f) {H T : Subgroup PSL(2, GaloisField p f)}
    (hT : Nat.card T = 2 ^ (Nat.card PSL(2, GaloisField p f)).factorization 2) (hTH : T ≤ H)
    {x : PSL(2, GaloisField p f)} (hx : orderOf x = 3)
    (hxT : x ∈ Subgroup.normalizer (T : Set PSL(2, GaloisField p f)))
    (hN : Subgroup.normalizer (Subgroup.zpowers x : Set PSL(2, GaloisField p f)) ≤ H) :
    H = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hT4 := card_sylow_eq_four_l2odd189 hp2 hp3 hf hT hx hxT
  have h8 := mod_eight_l2odd189 hp2 hf hT hT4
  have hfodd : Odd f := CFSG.Walter.odd_of_pow_mod_eight hpodd h8
  obtain ⟨hTc, -⟩ := not_isCyclic_sylow_l2odd189 hp2 hf hT
  have hT2 : IsPGroup 2 T := IsPGroup.of_card hT
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact Nat.not_prime_mul (by norm_num) (by norm_num) (show Nat.Prime (2 * 2) from hp)
  have hq5 : 5 ≤ p ^ f := le_trans hp5 (Nat.le_self_pow (by omega) p)
  letI : Fintype (GaloisField p f) := Fintype.ofFinite _
  classical
  have hFc : Fintype.card (GaloisField p f) = p ^ f := by rw [← Nat.card_eq_fintype_card, hK]
  have hchar : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have h3q : ¬ 3 ∣ Fintype.card (GaloisField p f) := by
    rw [hFc]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  obtain ⟨w, y, hwx, hyx, hy3, hy⟩ := exists_inv_comm_l2odd189 hchar (hFc ▸ hq5) h3q hx
  rw [hFc] at hy
  have hxH : x ∈ H := hN (Subgroup.le_normalizer (Subgroup.mem_zpowers x))
  have hwH : w ∈ H := by
    have h1 : w⁻¹ * x * w = x⁻¹ := by
      have h : w⁻¹ * x⁻¹ * w = x := by rw [← hwx]; group
      calc w⁻¹ * x * w = (w⁻¹ * x⁻¹ * w)⁻¹ := by group
        _ = x⁻¹ := by rw [h]
    refine hN (mem_normalizer_zpowers189 ?_ ?_)
    · rw [hwx]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
    · rw [h1]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
  have hyH : y ∈ H := by
    refine hN (mem_normalizer_zpowers189 ?_ ?_)
    · rw [hyx, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers x
    · rw [mul_assoc, ← hyx, inv_mul_cancel_left]
      exact Subgroup.mem_zpowers x
  have hkH : orderOf y ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hyH
  have hkp : Nat.Coprime (orderOf y) p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hpk
    have h1 : p ∣ p ^ f := dvd_pow_self p (by omega)
    have h2 : p ∣ orderOf y * 2 := dvd_mul_of_dvd_left hpk 2
    rcases hy with h | h <;> rw [h] at h2
    · have h3 := Nat.dvd_sub h1 h2
      rw [show p ^ f - (p ^ f - 1) = 1 by omega] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h2))
  rcases CFSG.Quasithin.F6.dicksonPSL2_holds p f hf H with
      ⟨-, m, -, hm⟩ | ⟨hc, -⟩ | ⟨z, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, hPn, -, hPcard, hPc, -⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, -⟩
  ·
    exfalso
    have h2 : 2 ∣ p ^ m := by
      rw [← hm]
      exact dvd_trans ⟨2, by omega⟩ (hT4 ▸ Subgroup.card_dvd_of_le hTH)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  · exact (hTc (Subgroup.isCyclic_of_le (H' := H) hTH)).elim
  · exact (false_of_dihedral_l2odd189 e hTH hTc hT2 hxH hx hxT).elim
  · exact (false_of_alternating_four_l2odd189 e hxH hwH hx hwx).elim
  ·
    exfalso
    rw [pow_mul'] at h16
    have := CFSG.Walter.sq_mod_sixteen_of_mod_eight h8
    omega
  ·
    by_cases hq : p ^ f = 5
    · apply Subgroup.eq_top_of_card_eq
      have hc := card_mul_two_l2odd189 hp2 (m := f) (by omega)
      rw [hq] at hc
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
      change 60 = _
      omega
    · exfalso
      have hk6 : 6 ≤ orderOf y := by omega
      have hko : orderOf (e ⟨y, hyH⟩) = orderOf y := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      rcases CFSG.Walter.alternatingGroup_five_pow_eq_one (e ⟨y, hyH⟩) with h | h | h <;>
      · have := Nat.le_of_dvd (by norm_num) (hko ▸ orderOf_dvd_of_pow_eq_one h)
        omega
  · have := hPn
    exact (false_of_borel_l2odd189 hTH hTc hT2 hp2 (IsPGroup.of_card hPcard) hPc).elim
  ·
    by_cases hmf : m = f
    · subst hmf
      exact Subgroup.eq_top_of_card_eq H (Nat.card_congr e.toEquiv)
    · exfalso
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [zero_dvd_iff] at hm
        omega
      obtain ⟨j, hj⟩ := hm
      have hjodd : Odd j := (Nat.odd_mul.mp (hj ▸ hfodd)).2
      have hj3 : 3 ≤ j := by
        obtain ⟨i, hi⟩ := hjodd
        rcases i with _ | i
        · exact absurd (by rw [hj, hi]; ring) hmf
        · omega
      have hr5 : 5 ≤ p ^ m := le_trans hp5 (Nat.le_self_pow hm0 p)
      have hqr : (p ^ m) ^ 3 ≤ p ^ f := by
        rw [← pow_mul, hj]
        exact Nat.pow_le_pow_right hp.pos (Nat.mul_le_mul_left m hj3)
      have hr3 : 5 * (p ^ m) ^ 2 ≤ (p ^ m) ^ 3 := by
        rw [pow_succ (p ^ m) 2, mul_comm]
        exact Nat.mul_le_mul_left _ hr5
      have hc := card_mul_two_l2odd189 hp2 hm0
      rw [← Nat.card_congr e.toEquiv] at hc
      have hk : orderOf y ∣ (p ^ m) ^ 2 - 1 :=
        (Nat.Coprime.pow_right m hkp).dvd_of_dvd_mul_left
          (hc ▸ dvd_mul_of_dvd_left hkH 2)
      have hr2 : 25 ≤ (p ^ m) ^ 2 := by nlinarith
      have := Nat.le_of_dvd (by omega) hk
      omega
  ·
    exact absurd (even_iff_two_dvd.mpr (dvd_trans (dvd_mul_right 2 m) hm))
      (Nat.not_even_iff_odd.mpr hfodd)

end CFSG.RankThree.PartTwo.Sec18
