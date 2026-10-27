module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABAABAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

private lemma s16h_e3_CycTwoP3M4AA2AABAABA_orbit_mul_stab
    [Finite W] [Finite (MulAut W)] (K : Subgroup (MulAut W)) (w : W) :
    (MulAction.orbit K w).ncard * Nat.card (MulAction.stabilizer K w) = Nat.card K := by
  rw [← MulAction.index_stabilizer, mul_comm]
  exact Subgroup.card_mul_index _

private lemma s16h_e3_CycTwoP3M4AA2AABAABA_card_elemAbelian
    {E : Subgroup (MulAut W)} (hE : IsElemAbelianOfRank 3 2 ↥E) :
    Nat.card ↥E = 9 := by
  obtain ⟨e⟩ := hE
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  decide

private lemma s16h_e3_CycTwoP3M4AA2AABAABA_of_orbit_three
    [Finite W] [Finite (MulAut W)]
    {z : MulAut W} (hzord : orderOf z = 3)
    (hfpf : ∀ w : W, z w = w → w = 1)
    {E : Subgroup (MulAut W)} (hE : IsElemAbelianOfRank 3 2 ↥E) (hzE : z ∈ E)
    {w : W} (hw : w ≠ 1) (h3 : (MulAction.orbit ↥E w).ncard = 3) :
    ∃ b ∈ E, orderOf b = 3 ∧ b ∉ Subgroup.zpowers z ∧ b w = w := by
  classical
  have hcardE : Nat.card ↥E = 9 :=
    s16h_e3_CycTwoP3M4AA2AABAABA_card_elemAbelian hE
  have hos := s16h_e3_CycTwoP3M4AA2AABAABA_orbit_mul_stab (K := E) w
  rw [h3, hcardE] at hos
  have hstab : Nat.card (MulAction.stabilizer ↥E w) = 3 := by omega
  have hdvd : 3 ∣ Nat.card (MulAction.stabilizer ↥E w) := ⟨1, by rw [hstab]⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card'
    (G := MulAction.stabilizer ↥E w) 3 hdvd
  have hbstab : (b : ↥E) ∈ MulAction.stabilizer ↥E w := b.property
  have hbE : ((b : ↥E) : MulAut W) ∈ E := (b : ↥E).property
  have hbEord : orderOf (b : ↥E) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hb
  have hbW : orderOf ((b : ↥E) : MulAut W) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hbEord
  have hbw : ((b : ↥E) : MulAut W) w = w := by
    have h := (MulAction.mem_stabilizer_iff).mp hbstab
    rw [MulAction.subgroup_smul_def] at h
    simpa using h
  refine ⟨((b : ↥E) : MulAut W), hbE, hbW, ?_, hbw⟩
  intro hmem
  have heq : Subgroup.zpowers ((b : ↥E) : MulAut W) = Subgroup.zpowers z := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
    simp [Nat.card_zpowers, hbW, hzord]
  have hzmem : z ∈ Subgroup.zpowers ((b : ↥E) : MulAut W) := by
    rw [heq]
    exact Subgroup.mem_zpowers z
  have hmemE : (⟨z, hzE⟩ : ↥E) ∈ Subgroup.zpowers (b : ↥E) := by
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzmem
    refine ⟨k, Subtype.ext ?_⟩
    simpa using hk
  have hzstab : (⟨z, hzE⟩ : ↥E) ∈ MulAction.stabilizer ↥E w :=
    (Subgroup.zpowers_le.mpr hbstab) hmemE
  have hzw : z w = w := by
    have h := (MulAction.mem_stabilizer_iff).mp hzstab
    rw [MulAction.subgroup_smul_def] at h
    simpa using h
  exact hw (hfpf w hzw)

theorem s16h_e3_CycTwoP3M4AA2AABAABA_two_e9_cover
    [Finite W] [Finite (MulAut W)]
    (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {z : MulAut W} (hzord : orderOf z = 3)
    (hfpf : ∀ w : W, z w = w → w = 1)
    {E E' : Subgroup (MulAut W)}
    (hE : IsElemAbelianOfRank 3 2 ↥E) (hE' : IsElemAbelianOfRank 3 2 ↥E')
    (hzE : z ∈ E) (hzE' : z ∈ E') (hne : E ≠ E') :
    ∀ w : W, w ≠ 1 →
      ∃ b ∈ E ⊔ E', orderOf b = 3 ∧ b ∉ Subgroup.zpowers z ∧ b w = w := by
  intro w hw
  have hcardE : Nat.card ↥E = 9 := s16h_e3_CycTwoP3M4AA2AABAABA_card_elemAbelian hE
  have hcardE' : Nat.card ↥E' = 9 := s16h_e3_CycTwoP3M4AA2AABAABA_card_elemAbelian hE'
  have hdvdE : (MulAction.orbit ↥E w).ncard ∣ 9 := by
    have h := s16h_e3_CycTwoP3M4AA2AABAABA_orbit_mul_stab (K := E) w
    rw [hcardE] at h
    exact ⟨Nat.card (MulAction.stabilizer ↥E w), h.symm⟩
  have hne1E : (MulAction.orbit ↥E w).ncard ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have hwmem : w ∈ MulAction.orbit ↥E w := MulAction.mem_orbit_self w
    have hzwmem : (⟨z, hzE⟩ : ↥E) • w ∈ MulAction.orbit ↥E w :=
      MulAction.mem_orbit_iff.mpr ⟨⟨z, hzE⟩, rfl⟩
    rw [ha] at hwmem hzwmem
    rw [Set.mem_singleton_iff] at hwmem hzwmem
    have hzw : (⟨z, hzE⟩ : ↥E) • w = w := hzwmem.trans hwmem.symm
    rw [MulAction.subgroup_smul_def] at hzw
    exact hw (hfpf w (by simpa using hzw))
  obtain ⟨kE, hkE2, hkE⟩ :=
    (Nat.dvd_prime_pow (p := 3) (m := 2) (by norm_num)).mp hdvdE
  have hdvdE' : (MulAction.orbit ↥E' w).ncard ∣ 9 := by
    have h := s16h_e3_CycTwoP3M4AA2AABAABA_orbit_mul_stab (K := E') w
    rw [hcardE'] at h
    exact ⟨Nat.card (MulAction.stabilizer ↥E' w), h.symm⟩
  have hne1E' : (MulAction.orbit ↥E' w).ncard ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have hwmem : w ∈ MulAction.orbit ↥E' w := MulAction.mem_orbit_self w
    have hzwmem : (⟨z, hzE'⟩ : ↥E') • w ∈ MulAction.orbit ↥E' w :=
      MulAction.mem_orbit_iff.mpr ⟨⟨z, hzE'⟩, rfl⟩
    rw [ha] at hwmem hzwmem
    rw [Set.mem_singleton_iff] at hwmem hzwmem
    have hzw : (⟨z, hzE'⟩ : ↥E') • w = w := hzwmem.trans hwmem.symm
    rw [MulAction.subgroup_smul_def] at hzw
    exact hw (hfpf w (by simpa using hzw))
  obtain ⟨kE', hkE'2, hkE'⟩ :=
    (Nat.dvd_prime_pow (p := 3) (m := 2) (by norm_num)).mp hdvdE'
  interval_cases kE
  · exact absurd (by simpa using hkE) hne1E
  · have h3 : (MulAction.orbit ↥E w).ncard = 3 := by simpa using hkE
    obtain ⟨b, hbE, hbo, hbnot, hbw⟩ :=
      s16h_e3_CycTwoP3M4AA2AABAABA_of_orbit_three hzord hfpf hE hzE hw h3
    exact ⟨b, Subgroup.mem_sup_left hbE, hbo, hbnot, hbw⟩
  · have h9 : (MulAction.orbit ↥E w).ncard = 9 := by simpa using hkE
    interval_cases kE'
    · exact absurd (by simpa using hkE') hne1E'
    · have h3 : (MulAction.orbit ↥E' w).ncard = 3 := by simpa using hkE'
      obtain ⟨b, hbE', hbo, hbnot, hbw⟩ :=
        s16h_e3_CycTwoP3M4AA2AABAABA_of_orbit_three hzord hfpf hE' hzE' hw h3
      exact ⟨b, Subgroup.mem_sup_right hbE', hbo, hbnot, hbw⟩
    · have h9' : (MulAction.orbit ↥E' w).ncard = 9 := by simpa using hkE'
      exact s16h_e3_CycTwoP3M4AA2AABAABAA_cover_of_nine hexp hcard hzord hfpf hE hE'
        hzE hzE' hne hw h9 h9'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
