module

public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.RankThree.PartOne.S9.QD32.AutCount

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.QD32Facts

theorem quaternionDihedralAutomorphismPrimeSupport :
    QuaternionDihedralAutomorphismPrimeSupport := by
  intro S _ hS
  obtain ⟨φ⟩ := hS
  have hcard : Nat.card (MulAut S) ∣ 2 ^ 7 * 3 * 5 := by
    rw [Nat.card_congr (MulAut.congr φ).toEquiv]
    exact card_mulAut_QD32_dvd
  refine ⟨hcard, ?_⟩
  intro q P _ _ hq hq5 hP f
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.one_apply]
  obtain ⟨k, hk⟩ := hP x
  have h1 : orderOf (f x) ∣ q ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  have h2 : orderOf (f x) ∣ 2 ^ 7 * 3 * 5 := (orderOf_dvd_natCard (f x)).trans hcard
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).mp h1
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · exfalso
    have hqd : q ∣ 2 ^ 7 * 3 * 5 := by
      refine dvd_trans ?_ h2
      rw [hj]
      exact dvd_pow_self q hjpos.ne'
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
    · rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
      · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h')
        omega
      · have := Nat.le_of_dvd (by norm_num) h'
        omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega

end CFSG.RankThree.PartOne
