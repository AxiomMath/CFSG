module

public import Certificates.Certificate946015
public import CFSG.RankThree.GF2n.Parrott.PSp43Model

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups


theorem e9_mem_A : e9 ∈ QA45.originalSubgroup :=
  (mem_iff_sift QA45 QA45_ok e9).2 Certificates.certificate946015.e9_mem_A

theorem e9_pow_nine : e9 ^ 9 = 1 := Certificates.certificate946015.e9_pow_nine

theorem e9_cube : e9 ^ 3 = sigma1 := Certificates.certificate946015.e9_cube

theorem e9_cube_ne_one : e9 ^ 3 ≠ 1 := Certificates.certificate946015.e9_cube_ne_one

theorem orderOf_e9 : orderOf e9 = 9 := by
  have hdvd : orderOf e9 ∣ 3 ^ 2 := by
    simpa using orderOf_dvd_of_pow_eq_one e9_pow_nine
  obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).mp hdvd
  have h3 : ¬ (orderOf e9 ∣ 3) := by
    intro h
    exact e9_cube_ne_one (orderOf_dvd_iff_pow_eq_one.mp h)
  interval_cases i
  · exfalso
    rw [hieq] at h3
    norm_num at h3
  · exfalso
    rw [hieq] at h3
    norm_num at h3
  · rw [hieq]
    norm_num

theorem exists_order_nine_cube_sigma1 :
    ∃ y : QA45.originalSubgroup, orderOf y = 9 ∧ y ^ 3 = ⟨sigma1, sigma1_mem_A⟩ := by
  refine ⟨⟨e9, e9_mem_A⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact orderOf_e9
  · apply Subtype.ext
    show e9 ^ 3 = sigma1
    exact e9_cube

end CFSG.RankThree.GF2n.Parrott
