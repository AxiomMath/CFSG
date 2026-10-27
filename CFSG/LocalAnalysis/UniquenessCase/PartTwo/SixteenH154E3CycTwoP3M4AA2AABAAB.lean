module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABAABA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

theorem s16h_e3_CycTwoP3M4AA2AABAAB_normal_of_elemAbelian
    [Finite W] [Finite (MulAut W)]
    (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {A : Subgroup (MulAut W)} {z : MulAut W}
    (hzA : z ∈ A) (hzord : orderOf z = 3)
    (hfpf : ∀ w : W, z w = w → w = 1)
    (hAn : A ≤ Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut W)))
    (hline : ∃ w : W, w ≠ 1 ∧ ∀ b ∈ A, b ≠ 1 → orderOf b = 3 → b w = w →
      b ∈ Subgroup.zpowers z)
    {E : Subgroup (MulAut W)} (hEA : E ≤ A) (hE : IsElemAbelianOfRank 3 2 ↥E) :
    (E.subgroupOf A).Normal := by
  classical
  have hEkeep := hE
  obtain ⟨eE⟩ := hEkeep
  have hcardE : Nat.card ↥E = 9 := by
    rw [Nat.card_congr eE.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hEp : IsPGroup 3 ↥E := IsPGroup.iff_card.mpr ⟨2, by rw [hcardE]; norm_num⟩
  have hZp : IsPGroup 3 ↥(Subgroup.zpowers z) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hzord, pow_one]⟩
  have hzE : z ∈ E := by
    have hHp : IsPGroup 3 ↥(E ⊔ Subgroup.zpowers z : Subgroup (MulAut W)) :=
      hEp.to_sup_of_normal_right' hZp (hEA.trans hAn)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
    have hdvd : 3 ^ k ∣ Nat.card (MulAut W) := by
      rw [← hk]
      exact Subgroup.card_subgroup_dvd_card (E ⊔ Subgroup.zpowers z)
    have hk2 : k ≤ 2 := by
      by_contra h
      exact s16h_e3_CycTwoP3M4AA2AABAAA_not_three_cube_dvd hexp hcard
        ((pow_dvd_pow 3 (by omega)).trans hdvd)
    have hle9 : Nat.card ↥(E ⊔ Subgroup.zpowers z : Subgroup (MulAut W)) ≤ 9 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 9 := by norm_num
    have h9dvd : 9 ∣ Nat.card ↥(E ⊔ Subgroup.zpowers z : Subgroup (MulAut W)) := by
      rw [← hcardE]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hHcard : Nat.card ↥(E ⊔ Subgroup.zpowers z : Subgroup (MulAut W)) = 9 :=
      le_antisymm hle9 (Nat.le_of_dvd (by norm_num) h9dvd)
    have hEq : E = E ⊔ Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hHcard, hcardE])
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hEA]
  by_contra hnot
  obtain ⟨a, haA, haN⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (E : Set (MulAut W)) := by
    by_contra h
    exact hnot fun a ha => by
      by_contra hmem
      exact h ⟨a, ha, hmem⟩
  let E' : Subgroup (MulAut W) := E.map (MulAut.conj a)
  have hE'ne : E ≠ E' := by
    intro h
    exact haN ((Subgroup.mem_normalizer_iff_map_conj_eq (H := E) (g := a)).mpr
      (by simpa [E'] using h.symm))
  have hE'A : E' ≤ A := by
    intro e he
    have he' : e ∈ E.map (MulAut.conj a) := he
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp he'
    rw [← hxe]
    exact A.mul_mem (A.mul_mem haA (hEA hx)) (A.inv_mem haA)
  have hE'el : IsElemAbelianOfRank 3 2 ↥E' :=
    ⟨(MulEquiv.subgroupMap (MulAut.conj a) E).symm.trans eE⟩
  have hzE' : z ∈ E' := by
    have hzainv : a⁻¹ * z * a ∈ E :=
      Subgroup.zpowers_le.mpr hzE
        ((Subgroup.mem_normalizer_iff.mp (hAn (A.inv_mem haA)) z).mp
          (Subgroup.mem_zpowers z))
    have hconj : (MulAut.conj a) (a⁻¹ * z * a) = a * (a⁻¹ * z * a) * a⁻¹ :=
      MulAut.conj_apply a (a⁻¹ * z * a)
    rw [show z = (MulAut.conj a) (a⁻¹ * z * a) by rw [hconj]; group]
    exact Subgroup.mem_map.mpr ⟨a⁻¹ * z * a, hzainv, rfl⟩
  obtain ⟨w, hw1, hw⟩ := hline
  obtain ⟨b, hbEE', hbord, hbnot, hbw⟩ :=
    s16h_e3_CycTwoP3M4AA2AABAABA_two_e9_cover hexp hcard hzord hfpf hE hE'el hzE hzE'
      hE'ne w hw1
  have hbA : b ∈ A := (sup_le hEA hE'A) hbEE'
  have hb1 : b ≠ 1 := by
    intro h
    rw [h] at hbord
    simp at hbord
  exact hbnot (hw b hbA hb1 hbord hbw)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
