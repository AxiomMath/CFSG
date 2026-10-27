module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM11Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreAssembly

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m11_rep_data :
    evalCodes [m11gA, m11gB] [1] ∈ m11Certificate.originalSubgroup ∧
      orderOf (evalCodes [m11gA, m11gB] [1]) = 2 ∧
      m11CentQ1.originalSubgroup ≤
        centralizerIn m11Certificate.originalSubgroup (evalCodes [m11gA, m11gB] [1]) ∧
      Nat.card m11CentQ1.originalSubgroup = 48 ∧ OddWitness m11CentQ1.originalSubgroup 3 := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hab : ∀ g ∈ [m11gA, m11gB], g ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]
    intro g hg
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact m11a.2
    · exact m11b.2
  obtain ⟨-, -, hord⟩ := m11_oddcore_cover
  obtain ⟨hc1, ho1, hcomm1, hw1⟩ := m11_oddcore_cent1
  refine ⟨evalCodes_mem _ hab _, ?_, ?_, ?_, oddWitness_of_oddWitnessOK hn _ hc1 hw1⟩
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (List.mem_singleton_self _))
  · rw [m11CentQ1, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ hab w) hcomm1
  · rw [← m11CentQ1.orderCertificate_eq_card hc1, ho1]

theorem m11_involution_centralizer_witness :
    ∀ u ∈ NativeSporadic.M11, orderOf u = 2 →
    ∃ mu vu : ℕ, Nat.card (centralizerIn NativeSporadic.M11 u) = 2 ^ vu * mu ∧
      OddWitness (centralizerIn NativeSporadic.M11 u) mu := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  obtain ⟨hok, hsz, -⟩ := m11_oddcore_cover
  obtain ⟨hr, hro, hK, hKc, hKw⟩ := m11_rep_data
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  simp only [repSizes, m11InvReps, m11InvRepWords, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] at hsz
  rw [← m11Certificate_originalSubgroup]
  intro u hu ho
  refine centralizer_witness_of_reps hn m11Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) [(evalCodes [m11gA, m11gB] [1], m11CentQ1.originalSubgroup,
      3, 4)] (by simpa using ⟨hr, hro⟩) 400 hok ?_ u (by simpa using hu) ho
  simp only [List.mem_singleton, forall_eq]
  refine ⟨hK, ?_, by rw [hKc]; norm_num, hKw⟩
  rw [hsz, hKc, m11Certificate_originalSubgroup, m11_card]

theorem m11_inner_oddCore
    (t : NativeSporadic.M11) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set NativeSporadic.M11)) = ⊥ :=
  inner_oddCore_eq_bot _ m11_involution_centralizer_witness t ht

theorem m11_mulAut_card :

    Nat.card (MulAut NativeSporadic.M11) ≤ Nat.card NativeSporadic.M11 := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  obtain ⟨hok, -, -⟩ := m11_oddcore_cover
  obtain ⟨hoa, hob, hws, htot⟩ := m11_oddcore_aut
  obtain ⟨hr, hro, -, -, -⟩ := m11_rep_data
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  have ha' : orderOf m11gA = 2 := (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m11gB = 4 := (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hpos : ∀ p ∈ m11AutWords, 0 < p.2 := by decide
  have hwr : WordsRel m11AutWords m11gA m11gB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) hpos).1 hws
  have hbound := card_mulAut_le_wordPairs m11a m11b m11_closure_eq_top m11AutWords
    ((wordsRel_coe (H := NativeSporadic.M11) m11AutWords m11a m11b).1 hwr)
  have hoa' : orderOf m11a = 2 := by rw [← Subgroup.orderOf_coe]; exact ha'
  have hob' : orderOf m11b = 4 := by rw [← Subgroup.orderOf_coe]; exact hb'
  rw [hoa', hob'] at hbound
  have hcount := card_pairs_eq_repsTotal hn m11Certificate hQ (mx := 2) (my := 4) (by norm_num)
    (by norm_num) hpos (pairTables_spec hn hA hB) [evalCodes [m11gA, m11gB] [1]]
    (by simpa using ⟨hr, hro⟩) 400 hok
  rw [show repsTotal 11 (pairTables m11gA m11gB) (pairTables m11gA⁻¹ m11gB⁻¹)
    ([evalCodes [m11gA, m11gB] [1]].map toTable) (orderTables m11Certificate 4) 400
    (wordsTest 11 2 4 m11AutWords) = 7920 from htot, m11Certificate_originalSubgroup] at hcount
  rw [m11_card]
  rw [hcount] at hbound
  exact hbound

theorem m11_gens_not_comm : m11a * m11b ≠ m11b * m11a := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hoa, hob, hws, -⟩ := m11_oddcore_aut
  have ha' : orderOf m11gA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m11gB = 4 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hwr : WordsRel m11AutWords m11gA m11gB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) (by decide)).1 hws
  have hc := (wordsRel_coe (H := NativeSporadic.M11) m11AutWords m11a m11b).1 hwr
    ([0, 1, 2, 3], 6) (by decide)
  rw [evalW_commutator] at hc
  exact mul_ne_mul_of_orderOf_commutator hc (by norm_num)

theorem m11_center_eq_bot' :
    Subgroup.center NativeSporadic.M11 = ⊥ :=
  center_eq_bot_of_simple fam_m11_simplicity.2.2 m11_gens_not_comm

theorem m11_outer_oddCore
    (α : MulAut NativeSporadic.M11) (_hα2 : α * α = 1)
    (hα : α ∉ inner NativeSporadic.M11) : CFSG.oddCore (fixSub α) = ⊥ :=
  (outer_vacuous_of_card_le m11_center_eq_bot' m11_mulAut_card α hα).elim

end CFSG.Sporadic.Schreier
