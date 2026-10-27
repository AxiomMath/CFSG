module

public import CFSG.Quasithin.H13.A5S1327h
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Assembly.LowTwoRank

namespace KGL2

theorem sq_sub_one_mod_sixteen {p : ℕ} (hp : p % 24 = 11 ∨ p % 24 = 13) :
    (p ^ 2 - 1) % 16 = 8 := by
  have h16 : p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 11 ∨ p % 16 = 13 := by omega
  have hsq : p ^ 2 % 16 = 9 := by
    rw [Nat.pow_mod]
    rcases h16 with h | h | h | h <;> rw [h]
  have hpos : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

end KGL2

open KGL2 in
theorem factL2Three_holds : FactL2Three := by
  intro p K _ _ hp hp24 hL2
  have hp11 : 11 ≤ p := by omega
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨-, hsimple⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity K 2 p 1 hL2
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hL2
  have hFp : Nat.card F = p := by rw [hF, pow_one]
  have hcard : Nat.card K = p * (p ^ 2 - 1) / 2 := by
    rw [Nat.card_congr (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).toEquiv,
      CFSG.GorensteinWalter.psl2_card_formula F ⟨p, 1, hp, hpodd, le_rfl, by rw [hFp, pow_one]⟩,
      hFp]
  have heven : 2 ∣ p * (p ^ 2 - 1) := by
    have h := Nat.Odd.sub_odd (hpodd.pow (n := 2)) odd_one
    exact Dvd.dvd.mul_left (even_iff_two_dvd.1 h) p
  have hK2 : Nat.card K * 2 = p * (p ^ 2 - 1) := by
    rw [hcard]
    exact Nat.div_mul_cancel heven
  have hpK : p ∣ Nat.card K := by
    have h : p ∣ Nat.card K * 2 := ⟨p ^ 2 - 1, hK2⟩
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  have hnc : ∃ a b : K, a * b ≠ b * a := by
    by_contra hcon
    have hcomm : ∀ a b : K, a * b = b * a := fun a b => by
      by_contra hab
      exact hcon ⟨a, b, hab⟩
    let _ : CommGroup K := { (inferInstance : Group K) with mul_comm := hcomm }
    have hprime := IsSimpleGroup.prime_card (α := K)
    have hKp : Nat.card K = p :=
      ((Nat.prime_dvd_prime_iff_eq hp hprime).1 hpK).symm
    rw [hKp] at hK2
    have h3 : p ^ 2 - 1 = 2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p) hK2.symm
    have : 121 ≤ p ^ 2 := by nlinarith
    omega
  refine ⟨CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hnc, ?_, ?_⟩
  ·
    intro b hb
    rw [hb] at hpK
    rcases (Nat.Prime.dvd_mul hp).1 hpK with h | h
    · have h60 : p ≤ 60 := Nat.le_of_dvd (by norm_num) h
      interval_cases p <;> omega
    · exact absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)
  ·
    intro P hP
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    have hdvd : 2 ^ k ∣ Nat.card K := hk ▸ Subgroup.card_subgroup_dvd_card P
    have h1 : 2 ^ (k + 1) ∣ p * (p ^ 2 - 1) := by
      rw [← hK2, pow_succ]
      exact Nat.mul_dvd_mul_right hdvd 2
    have hcop : Nat.Coprime (2 ^ (k + 1)) p :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hpodd)
    have h2 : 2 ^ (k + 1) ∣ p ^ 2 - 1 := (Nat.Coprime.dvd_mul_left hcop).1 h1
    have hk2 : k ≤ 2 := by
      by_contra hk3
      have h16 : 16 ∣ p ^ 2 - 1 :=
        (pow_dvd_pow 2 (by omega : 4 ≤ k + 1)).trans h2
      have := sq_sub_one_mod_sixteen hp24
      omega
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num

end CFSG.Quasithin.H13.A5
