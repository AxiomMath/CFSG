module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABAAA
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

theorem s16h_e3_CycTwoP3M4AA2AABBAAA_three_centralizes_z
    [Finite (MulAut W)]
    {A : Subgroup (MulAut W)} {z : MulAut W}
    (hzord : orderOf z = 3)
    (hAn : A ≤ Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut W)))
    {b : MulAut W} (hbA : b ∈ A) (hbo : orderOf b = 3) :
    b * z = z * b := by
  classical
  have hmem : b * z * b⁻¹ ∈ Subgroup.zpowers z :=
    (Subgroup.mem_normalizer_iff.mp (hAn hbA) z).mp (Subgroup.mem_zpowers z)
  rw [mem_zpowers_iff_mem_range_orderOf] at hmem
  rw [hzord] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hkz⟩ := hmem
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  interval_cases k
  · exfalso
    have h1 : z = 1 := by
      have h := congrArg (fun y => b⁻¹ * y * b) hkz.symm
      have hz : b⁻¹ * (b * z * b⁻¹) * b = z := by group
      rw [hz] at h
      simpa using h
    rw [h1] at hzord
    simp at hzord
  · rw [pow_one] at hkz
    have h : z * b = b * z := by
      conv_lhs => rw [hkz]
      group
    exact h.symm
  · exfalso
    have hconj : b * z * b⁻¹ = z⁻¹ := by
      have hz2 : z ^ 2 = z⁻¹ := by
        have h3 : z ^ 3 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
        have hmul : z ^ 2 * z = 1 := by rw [← pow_succ]; simpa using h3
        exact eq_inv_of_mul_eq_one_left hmul
      rw [← hkz, hz2]
    have hφ : MulAut.conj b z = z⁻¹ := hconj
    have hφ3 : (MulAut.conj b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
    have h1 : ((MulAut.conj b) ^ 3) z = z := by rw [hφ3, MulAut.one_apply]
    have h2 : ((MulAut.conj b) ^ 3) z = z⁻¹ := by
      have hpow : (MulAut.conj b) ^ 3 =
          MulAut.conj b * MulAut.conj b * MulAut.conj b := by
        rw [pow_succ, pow_succ, pow_one]
      rw [hpow]
      simp only [MulAut.mul_apply, hφ, map_inv, inv_inv]
    have hzeq : z = z⁻¹ := h1.symm.trans h2
    have hzsq : z * z = 1 := (inv_eq_iff_mul_eq_one).mp hzeq.symm
    have hdvd : orderOf z ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rwa [pow_two]
    rw [hzord] at hdvd
    norm_num at hdvd

theorem s16h_e3_CycTwoP3M4AA2AABBAAA_zpowers_le_of_normal
    [Finite W] [Finite (MulAut W)]
    (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {A : Subgroup (MulAut W)} {z : MulAut W} {E : Subgroup (MulAut W)}
    (hzord : orderOf z = 3) (hzA : z ∈ A) (hEA : E ≤ A)
    (hE : IsElemAbelianOfRank 3 2 ↥E) (hEnorm : (E.subgroupOf A).Normal) :
    Subgroup.zpowers z ≤ E := by
  classical
  obtain ⟨e⟩ := hE
  have hcardE : Nat.card E = 9 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hcardZ : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, hzord]
  rw [Subgroup.zpowers_le]
  by_contra hzE
  have hinf : E ⊓ Subgroup.zpowers z = ⊥ := by
    refine Subgroup.eq_bot_of_card_le (H := E ⊓ Subgroup.zpowers z) ?_
    have hdvd : Nat.card ↥(E ⊓ Subgroup.zpowers z) ∣ 3 := by
      rw [← hcardZ]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hne3 : Nat.card ↥(E ⊓ Subgroup.zpowers z) ≠ 3 := by
      intro h3
      have heq : E ⊓ Subgroup.zpowers z = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hcardZ])
      have hz : z ∈ E ⊓ Subgroup.zpowers z := by
        rw [heq]
        exact Subgroup.mem_zpowers z
      exact hzE (Subgroup.mem_inf.1 hz).1
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact le_of_eq h1
    · exact absurd h3 hne3
  have hdisj : Disjoint E (Subgroup.zpowers z) := by
    rw [disjoint_iff]
    exact hinf
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set (MulAut W)) := by
    rw [Subgroup.zpowers_le]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hEA).mp hEnorm hzA
  have hcard_sup := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    E (Subgroup.zpowers z) hnorm hdisj
  have hdvd : 3 ^ 3 ∣ Nat.card (MulAut W) := by
    let S : Subgroup (MulAut W) := E ⊔ Subgroup.zpowers z
    have hScard : Nat.card S = Nat.card E * Nat.card (Subgroup.zpowers z) := hcard_sup
    have h : Nat.card S ∣ Nat.card (MulAut W) := Subgroup.card_subgroup_dvd_card S
    rw [hScard, hcardE, hcardZ] at h
    change 27 ∣ Nat.card (MulAut W)
    norm_num at h
    exact h
  exact s16h_e3_CycTwoP3M4AA2AABAAA_not_three_cube_dvd hexp hcard hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
