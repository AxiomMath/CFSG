module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterCheck

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m22_delta_normalizes :
    ∀ h ∈ NativeSporadic.M22, m22Delta * h * m22Delta⁻¹ ∈ NativeSporadic.M22 := by
  obtain ⟨-, hsa, hsb, -⟩ := m22_outer_delta
  have hsift := (m22Certificate.schreier_chain_order m22Certificate_check).2.2.2.1
  refine conj_mem_of_closure m22_eq ?_
  intro s hs
  rw [← m22Certificate_originalSubgroup]
  rcases Set.mem_insert_iff.1 hs with rfl | hs
  · exact (hsift _).1 hsa
  · rw [Set.mem_singleton_iff] at hs
    subst hs
    exact (hsift _).1 hsb

theorem m22_delta_sq : m22Delta * m22Delta ∈ NativeSporadic.M22 := by
  rw [m22_outer_delta.1]
  exact one_mem _

theorem m22_delta_outer :
    ∀ g ∈ NativeSporadic.M22, ¬∀ h ∈ NativeSporadic.M22, m22Delta * g * h = h * (m22Delta * g) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  rw [← m22Certificate_originalSubgroup]
  exact not_centralizes_of_count hn m22Certificate m22Certificate_check
    (m22_gens_mem _ (by simp)) (m22_gens_mem _ (by simp)) m22_outer_delta.2.2.2

abbrev m22OutRep1 : Equiv.Perm (Fin 22) := m22OutReps.getD 0 1

abbrev m22OutRep2 : Equiv.Perm (Fin 22) := m22OutReps.getD 1 1

theorem m22OutReps_eq : m22OutReps = [m22OutRep1, m22OutRep2] := rfl

theorem m22OutRep1_eq :
    m22OutRep1 = evalCodes [m22gA, m22gB] (m22OutRepWords.getD 0 []) * m22Delta := rfl

theorem m22OutRep2_eq :
    m22OutRep2 = evalCodes [m22gA, m22gB] (m22OutRepWords.getD 1 []) * m22Delta := rfl

theorem m22_out_rep_data1 :
    m22Delta⁻¹ * m22OutRep1 ∈ m22Certificate.originalSubgroup ∧ orderOf m22OutRep1 = 2 ∧
      m22OutCentQ1.originalSubgroup ≤ centralizerIn m22Certificate.originalSubgroup m22OutRep1 ∧
      Nat.card m22OutCentQ1.originalSubgroup = 320 ∧
      OddWitness m22OutCentQ1.originalSubgroup 5 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m22_outer_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m22_outer_cent1
  refine ⟨?_, ?_, ?_, ?_, oddWitness_of_oddWitnessOK hn _ hc hw⟩
  · rw [m22OutRep1_eq, ← mul_assoc, m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq _
      (m22Certificate_originalSubgroup ▸ evalCodes_mem _ m22_gens_mem _)
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m22OutReps_eq]; simp))
  · rw [m22OutCentQ1, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m22_gens_mem w) hcomm
  · rw [← m22OutCentQ1.orderCertificate_eq_card hc, ho]

theorem m22_out_rep_data2 :
    m22Delta⁻¹ * m22OutRep2 ∈ m22Certificate.originalSubgroup ∧ orderOf m22OutRep2 = 2 ∧
      m22OutCentQ2.originalSubgroup ≤ centralizerIn m22Certificate.originalSubgroup m22OutRep2 ∧
      Nat.card m22OutCentQ2.originalSubgroup = 1344 ∧
      OddWitness m22OutCentQ2.originalSubgroup 21 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m22_outer_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m22_outer_cent2
  refine ⟨?_, ?_, ?_, ?_, oddWitness_of_oddWitnessOK hn _ hc hw⟩
  · rw [m22OutRep2_eq, ← mul_assoc, m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq _
      (m22Certificate_originalSubgroup ▸ evalCodes_mem _ m22_gens_mem _)
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m22OutReps_eq]; simp))
  · rw [m22OutCentQ2, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m22_gens_mem w) hcomm
  · rw [← m22OutCentQ2.orderCertificate_eq_card hc, ho]

theorem m22_outer_witness :
    ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
    ∃ mu vu : ℕ, Nat.card (centralizerIn NativeSporadic.M22 u) = 2 ^ vu * mu ∧
      OddWitness (centralizerIn NativeSporadic.M22 u) mu := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, hK1, hKc1, hKw1⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, hKw2⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22OutReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  refine centralizer_witness_of_reps hn m22Certificate hQ (pairTables_spec hn hA hB) m22Delta hg₀
    [(m22OutRep1, m22OutCentQ1.originalSubgroup, 5, 6),
      (m22OutRep2, m22OutCentQ2.originalSubgroup, 21, 6)] ?_ 2000 hok ?_ u hu ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hr1, hro1⟩
    · exact ⟨hr2, hro2⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · refine ⟨hK1, ?_, by rw [hKc1]; norm_num, hKw1⟩
      rw [hsz.1, hKc1, m22Certificate_originalSubgroup, m22_card]
    · refine ⟨hK2, ?_, by rw [hKc2]; norm_num, hKw2⟩
      rw [hsz.2, hKc2, m22Certificate_originalSubgroup, m22_card]

theorem m22_outer_oddCore
    (α : MulAut NativeSporadic.M22) (hα2 : α * α = 1)
    (hα : α ∉ inner NativeSporadic.M22) : CFSG.oddCore (fixSub α) = ⊥ :=
  outer_oddCore_eq_bot NativeSporadic.M22 m22Delta m22_delta_normalizes m22_delta_sq
    m22_center_eq_bot' m22_delta_outer m22_mulAut_card m22_outer_witness α hα2 hα

end CFSG.Sporadic.Schreier
