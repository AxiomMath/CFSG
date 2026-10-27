module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreAssembly
public import CFSG.Sporadic.Schreier.M23Check

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms

theorem m23_gens_mem : ∀ g ∈ [m23PermA, m23PermB], g ∈ m23Certificate.originalSubgroup := by
  rw [m23Certificate_originalSubgroup]
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact m23GenA.2
  · exact m23GenB.2

abbrev m23Rep1 : Equiv.Perm (Fin 23) := m23InvReps.getD 0 1

theorem m23InvReps_eq : m23InvReps = [m23Rep1] := rfl

theorem m23_rep_data1 :
    m23Rep1 ∈ m23Certificate.originalSubgroup ∧
      orderOf (m23Rep1) = 2 ∧
      m23CentQ1.originalSubgroup ≤
        centralizerIn m23Certificate.originalSubgroup (m23Rep1) ∧
      Nat.card m23CentQ1.originalSubgroup = 2688 ∧
      OddWitness m23CentQ1.originalSubgroup 21 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, hord⟩ := m23_oddcore_cover
  obtain ⟨hc, ho, hcomm, hw⟩ := m23_oddcore_cent1
  refine ⟨evalCodes_mem _ m23_gens_mem _, ?_, ?_, ?_, oddWitness_of_oddWitnessOK hn _ hc hw⟩
  · exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (by rw [m23InvReps_eq]; simp))
  · rw [m23CentQ1, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m23_gens_mem w) hcomm
  · rw [← m23CentQ1.orderCertificate_eq_card hc, ho]

theorem m23_involution_centralizer_witness :
    ∀ u ∈ NativeSporadic.M23, orderOf u = 2 →
    ∃ mu vu : ℕ, Nat.card (centralizerIn NativeSporadic.M23 u) = 2 ^ vu * mu ∧
      OddWitness (centralizerIn NativeSporadic.M23 u) mu := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, hKw1⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m23Certificate_originalSubgroup]
  intro u hu ho
  refine centralizer_witness_of_reps hn m23Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh)
    [(m23Rep1, m23CentQ1.originalSubgroup, 21, 7)]
    ?_ 4000 hok ?_ u (by simpa using hu) ho
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨by simpa using hr1, hro1⟩
  · intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    refine ⟨hK1, ?_, by rw [hKc1]; norm_num, hKw1⟩
    rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card]

theorem m23_inner_oddCore
    (t : NativeSporadic.M23) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set NativeSporadic.M23)) = ⊥ :=
  inner_oddCore_eq_bot _ m23_involution_centralizer_witness t ht

theorem m23_gens_not_comm :
    m23GenA * m23GenB ≠ m23GenB * m23GenA := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hoa, hob, hws, -⟩ := m23_oddcore_aut
  have ha' : orderOf m23PermA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m23PermB = 4 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hwr : WordsRel m23AutWords m23PermA m23PermB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) (by decide)).1 hws
  have hc := (wordsRel_coe (H := NativeSporadic.M23) m23AutWords m23GenA m23GenB).1 hwr
    ([0, 1, 2, 3], 6) (by decide)
  rw [evalW_commutator] at hc
  exact mul_ne_mul_of_orderOf_commutator hc (by norm_num)

theorem m23_center_eq_bot' :
    Subgroup.center NativeSporadic.M23 = ⊥ :=
  center_eq_bot_of_simple fam_m23_simplicity.2.2 m23_gens_not_comm

theorem m23_mulAut_card :
    Nat.card (MulAut NativeSporadic.M23) ≤ Nat.card NativeSporadic.M23 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, -, -⟩ := m23_oddcore_cover
  obtain ⟨hoa, hob, hws, htot⟩ := m23_oddcore_aut
  rw [m23InvReps_eq] at hok htot
  obtain ⟨hr1, hro1, -, -, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have ha' : orderOf m23PermA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m23PermB = 4 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hpos : ∀ p ∈ m23AutWords, 0 < p.2 := by decide
  have hwr : WordsRel m23AutWords m23PermA m23PermB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) hpos).1 hws
  have hbound := card_mulAut_le_wordPairs m23GenA m23GenB (closure_pair_eq_top m23_eq_closure _ _)
    m23AutWords ((wordsRel_coe (H := NativeSporadic.M23) m23AutWords m23GenA m23GenB).1 hwr)
  have hoa' : orderOf m23GenA = 2 := by rw [← Subgroup.orderOf_coe]; exact ha'
  have hob' : orderOf m23GenB = 4 := by rw [← Subgroup.orderOf_coe]; exact hb'
  rw [hoa', hob'] at hbound
  have hrepsA : ∀ r ∈ [m23Rep1], r ∈ m23Certificate.originalSubgroup ∧ orderOf r = 2 := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨hr1, hro1⟩
  have hcount := card_pairs_eq_repsTotal hn m23Certificate hQ (mx := 2) (my := 4) (by norm_num)
    (by norm_num) hpos (pairTables_spec hn hA hB) [m23Rep1] hrepsA 4000 hok
  rw [htot, m23Certificate_originalSubgroup] at hcount
  rw [hcount] at hbound
  rw [m23_card]
  exact hbound

theorem m23_outer_oddCore
    (α : MulAut NativeSporadic.M23) (_hα2 : α * α = 1)
    (hα : α ∉ inner NativeSporadic.M23) : CFSG.oddCore (fixSub α) = ⊥ :=
  (outer_vacuous_of_card_le m23_center_eq_bot' m23_mulAut_card α hα).elim

end CFSG.Sporadic.Schreier
