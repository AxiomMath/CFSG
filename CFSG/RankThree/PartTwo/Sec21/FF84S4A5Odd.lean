module

import CFSG.GH74.GLS.Stage1.Thm4.L96Perm
public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

theorem five_ten_sign : ∀ u : P8, u ^ 10 = 1 → u ^ 5 ≠ 1 → u ^ 5 ≠ u →
    Equiv.Perm.sign (u ^ 5) = -1 := by
  intro u h10 h5 h5u
  have hd10 : orderOf u ∣ 10 := orderOf_dvd_of_pow_eq_one h10
  have hn5 : ¬ orderOf u ∣ 5 := fun h => h5 (orderOf_dvd_iff_pow_eq_one.mp h)
  have hn4 : ¬ orderOf u ∣ 4 := by
    intro h
    apply h5u
    calc
      u ^ 5 = u ^ 4 * u := pow_succ u 4
      _ = u := by rw [orderOf_dvd_iff_pow_eq_one.mp h, one_mul]
  have horder : orderOf u = 10 := by
    have hsmall : ∀ n : Fin 11, (n : ℕ) ∣ 10 → ¬ (n : ℕ) ∣ 5 →
        ¬ (n : ℕ) ∣ 4 → (n : ℕ) = 10 := by decide +kernel
    exact hsmall ⟨orderOf u, Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd10)⟩
      hd10 hn5 hn4
  have hs : Equiv.Perm.sign u = -1 := by
    rcases Int.isUnit_eq_one_or (Equiv.Perm.sign u).isUnit with hs | hs
    · exact (CFSG.GH74.GLS.Stage1.Thm4.L96.no_order_ten_alt8 u (Units.ext hs) horder).elim
    · exact Units.ext hs
  rw [map_pow, hs]
  decide

theorem pow_five_of_sq_one (x : P8) (hx : x ^ 2 = 1) : x ^ 5 = x := by
  rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_succ, pow_mul, hx, one_pow, one_mul]

theorem A_cent_A5_odd (K' : Subgroup P8) (hK : K' ≤ A8s) (e5 : K' ≃* alternatingGroup (Fin 5))
    (c : P8) (hc : c.IsThreeCycle) (hcK : c ∈ K') : Odd (Nat.card ↥(CenS K' ⊓ A8s)) := by
  obtain ⟨p, hpK, hp5, hp1⟩ : ∃ p : P8, p ∈ K' ∧ p ^ 5 = 1 ∧ p ≠ 1 := by
    let y : alternatingGroup (Fin 5) := ⟨finRotate 5, mem_alternatingGroup.2 (by decide)⟩
    have hy5 : y ^ 5 = 1 := Subtype.ext (by decide)
    have hy1 : y ≠ 1 := fun h => by
      have h' : (finRotate 5 : Perm (Fin 5)) = 1 := congrArg Subtype.val h
      exact absurd h' (by decide)
    refine ⟨((e5.symm y : K') : P8), (e5.symm y).2, ?_, ?_⟩
    · have h5 : (e5.symm y) ^ 5 = 1 := by rw [← map_pow, hy5, map_one]
      simpa using congrArg Subtype.val h5
    · intro h
      have h1 : e5.symm y = 1 := Subtype.ext h
      apply hy1
      have h2 : e5 (e5.symm y) = e5 1 := by rw [h1]
      simpa using h2
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CenS K' ⊓ A8s)) 2 h2
  have hg2 : g ^ 2 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have ht2 : (g : P8) ^ 2 = 1 := by simpa using congrArg Subtype.val hg2
  have ht1 : (g : P8) ≠ 1 := by
    intro h
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    exact absurd hg (by decide)
  have hcomm : Commute p (g : P8) := by
    have hgc : (g : P8) ∈ CenS K' := g.2.1
    exact mem_centralizer_iff.1 hgc p hpK
  have hsign : sign (g : P8) = 1 := mem_alternatingGroup.1 g.2.2
  have hu5 : (p * g) ^ 5 = (g : P8) := by
    rw [hcomm.mul_pow, hp5, one_mul, pow_five_of_sq_one _ ht2]
  have hu10 : (p * g) ^ 10 = 1 := by
    rw [show (10 : ℕ) = 5 * 2 from rfl, pow_mul, hu5, ht2]
  have hu5ne1 : (p * g) ^ 5 ≠ 1 := by rw [hu5]; exact ht1
  have hu5neu : (p * g) ^ 5 ≠ p * g := by
    rw [hu5]
    intro h
    apply hp1
    have h' : p * (g : P8) = 1 * (g : P8) := by rw [one_mul]; exact h.symm
    exact mul_right_cancel h'
  have hsw := five_ten_sign (p * g) hu10 hu5ne1 hu5neu
  rw [hu5, hsign] at hsw
  exact absurd hsw (by decide)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
