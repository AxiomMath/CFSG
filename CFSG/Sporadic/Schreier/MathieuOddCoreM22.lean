module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreAssembly

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m22_gens_mem : ∀ g ∈ [m22gA, m22gB], g ∈ m22Certificate.originalSubgroup := by
  rw [m22Certificate_originalSubgroup]
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact m22a.2
  · exact m22b.2

abbrev m22Rep1 : Equiv.Perm (Fin 22) := m22InvReps.getD 0 1

theorem m22InvReps_eq : m22InvReps = [m22Rep1] := rfl

theorem m22_rep_data1 :
    m22Rep1 ∈ m22Certificate.originalSubgroup ∧
      orderOf (m22Rep1) = 2 ∧
      m22CentQ1.originalSubgroup ≤
        centralizerIn m22Certificate.originalSubgroup (m22Rep1) ∧
      Nat.card m22CentQ1.originalSubgroup = 384 ∧
      OddWitness m22CentQ1.originalSubgroup 3 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m22_oddcore_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m22_oddcore_cent1
  refine ⟨evalCodes_mem _ m22_gens_mem _, ?_, ?_, ?_, oddWitness_of_oddWitnessOK hn _ hc hw⟩
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m22InvReps_eq]; simp))
  · rw [m22CentQ1, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m22_gens_mem w) hcomm
  · rw [← m22CentQ1.orderCertificate_eq_card hc, ho]

theorem m22_involution_centralizer_witness :
    ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
    ∃ mu vu : ℕ, Nat.card (centralizerIn NativeSporadic.M22 u) = 2 ^ vu * mu ∧
      OddWitness (centralizerIn NativeSporadic.M22 u) mu := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, hKw1⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  refine centralizer_witness_of_reps hn m22Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh)
    [(m22Rep1, m22CentQ1.originalSubgroup, 3, 7)]
    ?_ 2000 hok ?_ u (by simpa using hu) ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨by simpa using hr1, hro1⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    refine ⟨hK1, ?_, by rw [hKc1]; norm_num, hKw1⟩
    rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card]

theorem m22_inner_oddCore
    (t : NativeSporadic.M22) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set NativeSporadic.M22)) = ⊥ :=
  inner_oddCore_eq_bot _ m22_involution_centralizer_witness t ht

theorem m22_gens_not_comm : m22a * m22b ≠ m22b * m22a := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hoa, hob, hws, -⟩ := m22_oddcore_aut
  have ha' : orderOf m22gA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m22gB = 4 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hwr : WordsRel m22AutWords m22gA m22gB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) (by decide)).1 hws
  have hc := (wordsRel_coe (H := NativeSporadic.M22) m22AutWords m22a m22b).1 hwr
    ([0, 1, 2, 3], 6) (by decide)
  rw [evalW_commutator] at hc
  exact mul_ne_mul_of_orderOf_commutator hc (by norm_num)

theorem m22_center_eq_bot' :
    Subgroup.center NativeSporadic.M22 = ⊥ :=
  center_eq_bot_of_simple fam_m22_simplicity.2.2 m22_gens_not_comm

theorem m22_mulAut_card :
    Nat.card (MulAut NativeSporadic.M22) ≤ 2 * Nat.card NativeSporadic.M22 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, -⟩ := m22_oddcore_cover
  obtain ⟨hoa, hob, hws, htot⟩ := m22_oddcore_aut
  rw [m22InvReps_eq] at hok htot
  obtain ⟨hr1, hro1, -, -, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have ha' : orderOf m22gA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m22gB = 4 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hpos : ∀ p ∈ m22AutWords, 0 < p.2 := by decide
  have hwr : WordsRel m22AutWords m22gA m22gB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) hpos).1 hws
  have hbound := card_mulAut_le_wordPairs m22a m22b (closure_pair_eq_top m22_eq _ _)
    m22AutWords ((wordsRel_coe (H := NativeSporadic.M22) m22AutWords m22a m22b).1 hwr)
  have hoa' : orderOf m22a = 2 := by rw [← Subgroup.orderOf_coe]; exact ha'
  have hob' : orderOf m22b = 4 := by rw [← Subgroup.orderOf_coe]; exact hb'
  rw [hoa', hob'] at hbound
  have hrepsA : ∀ r ∈ [m22Rep1], r ∈ m22Certificate.originalSubgroup ∧ orderOf r = 2 := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨hr1, hro1⟩
  have hcount := card_pairs_eq_repsTotal hn m22Certificate hQ (mx := 2) (my := 4) (by norm_num)
    (by norm_num) hpos (pairTables_spec hn hA hB) [m22Rep1] hrepsA 2000 hok
  rw [htot, m22Certificate_originalSubgroup] at hcount
  rw [hcount] at hbound
  rw [m22_card]
  exact hbound

end CFSG.Sporadic.Schreier
