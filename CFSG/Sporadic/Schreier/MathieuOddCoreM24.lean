module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreAssembly
public import CFSG.Sporadic.Schreier.M24Check

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m24_gens_mem : ∀ g ∈ [m24gA, m24gB], g ∈ m24Certificate.originalSubgroup := by
  rw [m24Certificate_originalSubgroup]
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact m24a.2
  · exact m24b.2

abbrev m24Rep1 : Equiv.Perm (Fin 24) := m24InvReps.getD 0 1

abbrev m24Rep2 : Equiv.Perm (Fin 24) := m24InvReps.getD 1 1

theorem m24InvReps_eq : m24InvReps = [m24Rep1, m24Rep2] := rfl

theorem m24_rep_data1 :
    m24Rep1 ∈ m24Certificate.originalSubgroup ∧
      orderOf (m24Rep1) = 2 ∧
      m24CentQ1.originalSubgroup ≤
        centralizerIn m24Certificate.originalSubgroup (m24Rep1) ∧
      Nat.card m24CentQ1.originalSubgroup = 7680 ∧
      OddWitness m24CentQ1.originalSubgroup 15 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m24_oddcore_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m24_oddcore_cent1
  refine ⟨evalCodes_mem _ m24_gens_mem _, ?_, ?_, ?_, oddWitness_of_oddWitnessOK hn _ hc hw⟩
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m24InvReps_eq]; simp))
  · rw [m24CentQ1, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m24_gens_mem w) hcomm
  · rw [← m24CentQ1.orderCertificate_eq_card hc, ho]

theorem m24_rep_data2 :
    m24Rep2 ∈ m24Certificate.originalSubgroup ∧
      orderOf (m24Rep2) = 2 ∧
      m24CentQ2.originalSubgroup ≤
        centralizerIn m24Certificate.originalSubgroup (m24Rep2) ∧
      Nat.card m24CentQ2.originalSubgroup = 21504 ∧
      OddWitness m24CentQ2.originalSubgroup 21 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m24_oddcore_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m24_oddcore_cent2
  refine ⟨evalCodes_mem _ m24_gens_mem _, ?_, ?_, ?_, oddWitness_of_oddWitnessOK hn _ hc hw⟩
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m24InvReps_eq]; simp))
  · rw [m24CentQ2, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m24_gens_mem w) hcomm
  · rw [← m24CentQ2.orderCertificate_eq_card hc, ho]

theorem m24_involution_centralizer_witness :
    ∀ u ∈ NativeSporadic.M24, orderOf u = 2 →
    ∃ mu vu : ℕ, Nat.card (centralizerIn NativeSporadic.M24 u) = 2 ^ vu * mu ∧
      OddWitness (centralizerIn NativeSporadic.M24 u) mu := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  obtain ⟨hok, hsz, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, hKw1⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, hKw2⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  rw [m24InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m24Certificate_originalSubgroup]
  intro u hu ho
  refine centralizer_witness_of_reps hn m24Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh)
    [(m24Rep1, m24CentQ1.originalSubgroup, 15, 9), (m24Rep2, m24CentQ2.originalSubgroup, 21, 10)]
    ?_ 40000 hok ?_ u (by simpa using hu) ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨by simpa using hr1, hro1⟩
    · exact ⟨by simpa using hr2, hro2⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · refine ⟨hK1, ?_, by rw [hKc1]; norm_num, hKw1⟩
      rw [hsz.1, hKc1, m24Certificate_originalSubgroup, m24_card]
    · refine ⟨hK2, ?_, by rw [hKc2]; norm_num, hKw2⟩
      rw [hsz.2, hKc2, m24Certificate_originalSubgroup, m24_card]

theorem m24_inner_oddCore
    (t : NativeSporadic.M24) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set NativeSporadic.M24)) = ⊥ :=
  inner_oddCore_eq_bot _ m24_involution_centralizer_witness t ht

theorem m24_gens_not_comm : m24a * m24b ≠ m24b * m24a := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hoa, hob, hws, -⟩ := m24_oddcore_aut
  have ha' : orderOf m24gA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m24gB = 3 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hwr : WordsRel m24AutWords m24gA m24gB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) (by decide)).1 hws
  have hc := (wordsRel_coe (H := NativeSporadic.M24) m24AutWords m24a m24b).1 hwr
    ([0, 1, 2, 3], 12) (by decide)
  rw [evalW_commutator] at hc
  exact mul_ne_mul_of_orderOf_commutator hc (by norm_num)

theorem m24_center_eq_bot' :
    Subgroup.center NativeSporadic.M24 = ⊥ :=
  center_eq_bot_of_simple fam_m24_simplicity.2.2 m24_gens_not_comm

theorem m24_mulAut_card :
    Nat.card (MulAut NativeSporadic.M24) ≤ Nat.card NativeSporadic.M24 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  obtain ⟨hok, -, -⟩ := m24_oddcore_cover
  obtain ⟨hoa, hob, hws, htot⟩ := m24_oddcore_aut
  rw [m24InvReps_eq] at hok htot
  obtain ⟨hr1, hro1, -, -, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, -, -, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have ha' : orderOf m24gA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m24gB = 3 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hpos : ∀ p ∈ m24AutWords, 0 < p.2 := by decide
  have hwr : WordsRel m24AutWords m24gA m24gB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) hpos).1 hws
  have hbound := card_mulAut_le_wordPairs m24a m24b (closure_pair_eq_top m24_eq _ _)
    m24AutWords ((wordsRel_coe (H := NativeSporadic.M24) m24AutWords m24a m24b).1 hwr)
  have hoa' : orderOf m24a = 2 := by rw [← Subgroup.orderOf_coe]; exact ha'
  have hob' : orderOf m24b = 3 := by rw [← Subgroup.orderOf_coe]; exact hb'
  rw [hoa', hob'] at hbound
  have hrepsA : ∀ r ∈ [m24Rep1, m24Rep2], r ∈ m24Certificate.originalSubgroup ∧ orderOf r = 2 := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨hr1, hro1⟩
    · exact ⟨hr2, hro2⟩
  have hcount := card_pairs_eq_repsTotal hn m24Certificate hQ (mx := 2) (my := 3) (by norm_num)
    (by norm_num) hpos (pairTables_spec hn hA hB) [m24Rep1, m24Rep2] hrepsA 40000 hok
  rw [htot, m24Certificate_originalSubgroup] at hcount
  rw [hcount] at hbound
  rw [m24_card]
  exact hbound

theorem m24_outer_oddCore
    (α : MulAut NativeSporadic.M24) (_hα2 : α * α = 1)
    (hα : α ∉ inner NativeSporadic.M24) : CFSG.oddCore (fixSub α) = ⊥ :=
  (outer_vacuous_of_card_le m24_center_eq_bot' m24_mulAut_card α hα).elim

end CFSG.Sporadic.Schreier
