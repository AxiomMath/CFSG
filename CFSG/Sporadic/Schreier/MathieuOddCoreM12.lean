module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreAssembly

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m12_gens_mem : ∀ g ∈ [m12gA, m12gB], g ∈ m12Certificate.originalSubgroup := by
  rw [m12Certificate_originalSubgroup]
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact m12a.2
  · exact m12b.2

abbrev m12Rep1 : Equiv.Perm (Fin 12) := m12InvReps.getD 0 1

abbrev m12Rep2 : Equiv.Perm (Fin 12) := m12InvReps.getD 1 1

theorem m12InvReps_eq : m12InvReps = [m12Rep1, m12Rep2] := rfl

theorem m12_rep_data1 :
    m12Rep1 ∈ m12Certificate.originalSubgroup ∧
      orderOf (m12Rep1) = 2 ∧
      m12CentQ1.originalSubgroup ≤
        centralizerIn m12Certificate.originalSubgroup (m12Rep1) ∧
      Nat.card m12CentQ1.originalSubgroup = 192 ∧
      OddWitness m12CentQ1.originalSubgroup 3 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m12_oddcore_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m12_oddcore_cent1
  refine ⟨evalCodes_mem _ m12_gens_mem _, ?_, ?_, ?_, oddWitness_of_oddWitnessOK hn _ hc hw⟩
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m12InvReps_eq]; simp))
  · rw [m12CentQ1, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m12_gens_mem w) hcomm
  · rw [← m12CentQ1.orderCertificate_eq_card hc, ho]

theorem m12_rep_data2 :
    m12Rep2 ∈ m12Certificate.originalSubgroup ∧
      orderOf (m12Rep2) = 2 ∧
      m12CentQ2.originalSubgroup ≤
        centralizerIn m12Certificate.originalSubgroup (m12Rep2) ∧
      Nat.card m12CentQ2.originalSubgroup = 240 ∧
      OddWitness m12CentQ2.originalSubgroup 15 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m12_oddcore_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m12_oddcore_cent2
  refine ⟨evalCodes_mem _ m12_gens_mem _, ?_, ?_, ?_, oddWitness_of_oddWitnessOK hn _ hc hw⟩
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m12InvReps_eq]; simp))
  · rw [m12CentQ2, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m12_gens_mem w) hcomm
  · rw [← m12CentQ2.orderCertificate_eq_card hc, ho]

theorem m12_involution_centralizer_witness :
    ∀ u ∈ NativeSporadic.M12, orderOf u = 2 →
    ∃ mu vu : ℕ, Nat.card (centralizerIn NativeSporadic.M12 u) = 2 ^ vu * mu ∧
      OddWitness (centralizerIn NativeSporadic.M12 u) mu := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨hok, hsz, -⟩ := m12_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, hKw1⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, hKw2⟩ := m12_rep_data2
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  rw [m12InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m12Certificate_originalSubgroup]
  intro u hu ho
  refine centralizer_witness_of_reps hn m12Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh)
    [(m12Rep1, m12CentQ1.originalSubgroup, 3, 6), (m12Rep2, m12CentQ2.originalSubgroup, 15, 4)]
    ?_ 1000 hok ?_ u (by simpa using hu) ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨by simpa using hr1, hro1⟩
    · exact ⟨by simpa using hr2, hro2⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · refine ⟨hK1, ?_, by rw [hKc1]; norm_num, hKw1⟩
      rw [hsz.1, hKc1, m12Certificate_originalSubgroup, m12_card]
    · refine ⟨hK2, ?_, by rw [hKc2]; norm_num, hKw2⟩
      rw [hsz.2, hKc2, m12Certificate_originalSubgroup, m12_card]

theorem m12_inner_oddCore
    (t : NativeSporadic.M12) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set NativeSporadic.M12)) = ⊥ :=
  inner_oddCore_eq_bot _ m12_involution_centralizer_witness t ht

theorem m12_gens_not_comm : m12a * m12b ≠ m12b * m12a := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hoa, hob, hws, -⟩ := m12_oddcore_aut
  have ha' : orderOf m12gA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m12gB = 3 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hwr : WordsRel m12AutWords m12gA m12gB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) (by decide)).1 hws
  have hc := (wordsRel_coe (H := NativeSporadic.M12) m12AutWords m12a m12b).1 hwr
    ([0, 1, 2, 3], 6) (by decide)
  rw [evalW_commutator] at hc
  exact mul_ne_mul_of_orderOf_commutator hc (by norm_num)

theorem m12_center_eq_bot' :
    Subgroup.center NativeSporadic.M12 = ⊥ :=
  center_eq_bot_of_simple fam_m12_simplicity.2.2 m12_gens_not_comm

theorem m12_mulAut_card :
    Nat.card (MulAut NativeSporadic.M12) ≤ 2 * Nat.card NativeSporadic.M12 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨hok, -, -⟩ := m12_oddcore_cover
  obtain ⟨hoa, hob, hws, htot⟩ := m12_oddcore_aut
  rw [m12InvReps_eq] at hok htot
  obtain ⟨hr1, hro1, -, -, -⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, -, -, -⟩ := m12_rep_data2
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have ha' : orderOf m12gA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m12gB = 3 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hpos : ∀ p ∈ m12AutWords, 0 < p.2 := by decide
  have hwr : WordsRel m12AutWords m12gA m12gB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) hpos).1 hws
  have hbound := card_mulAut_le_wordPairs m12a m12b (closure_pair_eq_top m12_eq _ _)
    m12AutWords ((wordsRel_coe (H := NativeSporadic.M12) m12AutWords m12a m12b).1 hwr)
  have hoa' : orderOf m12a = 2 := by rw [← Subgroup.orderOf_coe]; exact ha'
  have hob' : orderOf m12b = 3 := by rw [← Subgroup.orderOf_coe]; exact hb'
  rw [hoa', hob'] at hbound
  have hrepsA : ∀ r ∈ [m12Rep1, m12Rep2], r ∈ m12Certificate.originalSubgroup ∧ orderOf r = 2 := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hr1, hro1⟩
    · exact ⟨hr2, hro2⟩
  have hcount := card_pairs_eq_repsTotal hn m12Certificate hQ (mx := 2) (my := 3) (by norm_num)
    (by norm_num) hpos (pairTables_spec hn hA hB) [m12Rep1, m12Rep2] hrepsA 1000 hok
  rw [htot, m12Certificate_originalSubgroup] at hcount
  rw [hcount] at hbound
  rw [m12_card]
  exact hbound

end CFSG.Sporadic.Schreier
