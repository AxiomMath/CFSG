module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Inputs
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Pairing
public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5Y6

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

theorem str83G4_caseB_data
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hR : ¬ str83R L1 L2 S ≤ Q1 L1 L2 S) :
    IsElemAbelian 2 (str83X L1 L2 S) ∧ ∃ d : Str83G4Data L1 L2 S,
      ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S := by
  refine ⟨str83G4S1_of_z2Comm str83G4Z2Comm_holds G L1 L2 S a hfr, ?_⟩
  obtain ⟨d₀⟩ := str83G4Data_nonempty hfr
  exact ⟨d₀, fun hc => hR ((str83G4_str83R_le_q1_iff hfr d₀).mpr hc)⟩

theorem str83G4XIndex_holds :
    Str83G4XIndex := by
  intro G _ _ L1 L2 S a hfr hR
  obtain ⟨hX, d₀, hB₀⟩ := str83G4_caseB_data hfr hR
  exact str83G4_relIndex_z1_x hfr d₀ hX hB₀

theorem str83G4Q1Index_holds :
    Str83G4Q1Index := by
  intro G _ _ L1 L2 S a hfr hR
  obtain ⟨hX, d₀, hB₀⟩ := str83G4_caseB_data hfr hR
  exact str83G4_relIndex_y_q1 hfr d₀ hX hB₀

theorem str83G4YIndex_holds :
    Str83G4YIndex := by
  intro G _ _ L1 L2 S a hfr hR
  obtain ⟨hX, d₀, hB₀⟩ := str83G4_caseB_data hfr hR
  obtain ⟨d, -, -, hB, hW⟩ :=
    str83G4_exists_data_d1_sup_conjugate_d1 hfr d₀ hX hB₀
  have hXI := str83G4_x_inf_centralizer_conjugate_x hfr d hX hB
  have hIX := str83G4_relIndex_x_inf_conjugate_x hfr d hX hB
  have hXstep := str83G4_isChiefStep_x_z1 hfr d hX hB
  have hIL2 := str83G4_commutator_mem_z2_of_mem_x_inf_conjugate hfr d hX hB
  have hD1I := str83G4_eq_one_of_mem_d1_of_commutator_mem_z2 hfr d hX hB
  have hfpf := str83G4_mem_z1_of_commutator_mem_z1 hfr d hX hB
  have hZ2 := str83G4_isChiefStep_z2 hfr d hX hB
  have hδ₂ := str83G4_eq_one_of_mem_d1_of_trivial_l2 hfr d hX hB
  have hQstep := str83G4_isChiefStep_q1_y hfr d hX hB
  have hYB := str83G4_y_inf_centralizer_eq_of_leaves hfr d hX hB hW hXstep hXI hIL2 hD1I
    hZ2 hδ₂ hQstep
  have h1q := str83G4_relIndex_x_y_eq_one_or hfr d hX hB hXI hIX hQstep hfpf hYB
  exact str83G4_relIndex_x_y_eq_of_eq_one_or hfr d hX hB h1q

theorem str83G4CaseBOrder_holds :
    Str83G4CaseBOrder :=
  str83G4CaseBOrder_of_parts (str83G4S1_of_z2Comm str83G4Z2Comm_holds)
    str83G4Z1Card_holds str83G4XIndex_holds str83G4YIndex_holds str83G4Q1Index_holds

theorem str83Q1Order_of_caseAFalse
    (hA : Str83G4CaseAFalse) : Str83Q1Order :=
  str83Q1Order_of_cases hA str83G4CaseBOrder_holds

end CFSG.Quasithin.Stroth

end
