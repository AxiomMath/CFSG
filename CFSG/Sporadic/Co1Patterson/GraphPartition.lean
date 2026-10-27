module

public import CFSG.Sporadic.Co1Patterson.GraphCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)


theorem suborbCheck5_parts :
    (ptSet orbE).contains (Native.mul (Native.mul (repXi 1) (repRows 4)) (repX 1)) = true ∧
    (ptSet orb4c).contains (Native.mul (Native.mul (repXi 1) (repRows 8)) (repX 1)) = true ∧
    (ptSet orb4c).contains (Native.mul (Native.mul (repXi 0) (repRows 5)) (repX 0)) = true ∧
    conjValid orbE (repX 1) (repXi 1) (repRows 4) = true ∧
    conjValid orbE (repX 1) (repXi 1) (repRows 8) = true ∧
    conjValid orbQ (repX 0) (repXi 0) (repRows 5) = true ∧
    countN orbE (repX 1) (repXi 1) (ptSet orbE) (repRows 4) = 45 ∧
    countN orbE (repX 1) (repXi 1) (ptSet orb4c) (repRows 8) = 25 ∧
    countN orbQ (repX 0) (repXi 0) (ptSet orb4c) (repRows 5) = 9 ∧
    fibreOK gensKe eRows (repRows 4) 2048 (treeT fib4Masks) = true ∧
    fibreOK gensKe eRows (repRows 8) 24576 (treeT fib8Masks) = true ∧
    fibreOK gensKz zRows (repRows 5) 16384 (treeT fib5Masks) = true := by
  have h := suborb_check5
  unfold suborbCheck5 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem nrep_conj_rep {j i : ℕ} (hj : j < 10) (hi : i < 10) :
    NRep (Native.mul (Native.mul (repXi j) (repRows i)) (repX j))
      (((gElt (repJ j))⁻¹ • repV i : Vt) : NativeSporadic.Co1) := by
  rw [coe_smul_conjVert, inv_inv]
  exact ((nrep_repXi dagOK_true hj).mul (nrep_repV hi)).mul (nrep_repX dagOK_true j)

theorem orbRel_of_contains {o : Orb} {root : Native.Rows} {n j i : ℕ} (hj : j < 10)
    (hi : i < 10) (h : exactOK o root n = true) {t : Vt} (ht : NRep root t)
    (hc : (ptSet o).contains (Native.mul (Native.mul (repXi j) (repRows i)) (repX j)) = true) :
    orbRel t (repV j) (repV i) := by
  rw [repV_eq_smul j, orbRel_smul_iff_mem]
  exact mem_cOrb_of_contains h ht (nrep_conj_rep hj hi) hc

theorem le_ncard_rep11 : ∀ i < 11, orbSize.getD i 0 ≤ (cOrb (rep11V i)).ncard := by
  obtain ⟨c1, c2, c3, v1, v2, v3, n1, n2, n3, f1, f2, f3⟩ := suborbCheck5_parts
  obtain ⟨a1, a2, a3, g1, g2, g3⟩ := suborbCheck4_parts
  have he := ncard_cOrb_e
  have hz := ncard_cOrb_z
  intro i hi
  interval_cases i
  · rw [rep11V_zero]
    exact Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (Set.toFinite _)).2
      ⟨vA, mem_cOrb_self vA⟩).ne'
  · rw [rep11V_succ, hz]; rfl
  · rw [rep11V_succ, he]; rfl
  · rw [rep11V_succ]; exact le_ncard_cOrb_A4
  · rw [rep11V_succ, ncard_cOrb_4c]; rfl
  ·
    rw [rep11V_succ]
    have hrel := orbRel_of_contains (by norm_num) (by norm_num) exact_orbE nrep_eRows c1
    have hm := fibre_le dagOK_true f1 nrep_eRows (nrep_repV (by norm_num))
    have hn := ncard_rel_le_countN exact_orbE exact_orbE v1 (nrep_repX dagOK_true 1)
      (nrep_repXi dagOK_true (by norm_num)) nrep_eRows (nrep_repV (by norm_num))
    rw [n1] at hn
    have := incidence_le hrel hm hn
    rw [he] at this
    show 573440 ≤ _
    omega
  ·
    rw [rep11V_succ]
    have hrel := orbRel_of_contains (by norm_num) (by norm_num) exact_orb4c
      (nrep_repV (by norm_num)) c3
    have hm := fibre_le dagOK_true f3 nrep_zRows (nrep_repV (by norm_num))
    have hn := ncard_rel_le_countN exact_orbQ exact_orb4c v3 (nrep_repX dagOK_true 0)
      (nrep_repXi dagOK_true (by norm_num)) (nrep_repV (by norm_num)) (nrep_repV (by norm_num))
    rw [n3] at hn
    have := incidence_le hrel hm hn
    rw [hz] at this
    show 491520 ≤ _
    omega
  · rw [rep11V_succ]
    have := anchor_le (by norm_num) a1 g1
    show 4838400 ≤ _
    omega
  · rw [rep11V_succ]
    have := anchor_le (by norm_num) a2 g2
    show 2419200 ≤ _
    omega
  ·
    rw [rep11V_succ]
    have hrel := orbRel_of_contains (by norm_num) (by norm_num) exact_orb4c
      (nrep_repV (by norm_num)) c2
    have hm := fibre_le dagOK_true f2 nrep_eRows (nrep_repV (by norm_num))
    have hn := ncard_rel_le_countN exact_orbE exact_orb4c v2 (nrep_repX dagOK_true 1)
      (nrep_repXi dagOK_true (by norm_num)) (nrep_repV (by norm_num)) (nrep_repV (by norm_num))
    rw [n2] at hn
    have := incidence_le hrel hm hn
    rw [he] at this
    show 12386304 ≤ _
    omega
  · rw [rep11V_succ]
    have := anchor_le (by norm_num) a3 g3
    show 25804800 ≤ _
    omega

theorem suborbits_cover (v : Vt) : ∃ i < 11, v ∈ cOrb (rep11V i) := by
  classical
  by_contra hv
  push Not at hv
  let F : ℕ → Finset Vt := fun i => (Set.toFinite (cOrb (rep11V i))).toFinset
  have hdisj : ((Finset.range 11 : Finset ℕ) : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hij
    refine Finset.disjoint_left.2 fun w hwi hwj => hij ?_
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact cOrb_disjoint hi hj ((Set.Finite.mem_toFinset _).1 hwi)
      ((Set.Finite.mem_toFinset _).1 hwj)
  have hU := Finset.card_biUnion hdisj
  have hsum0 : ∑ i ∈ Finset.range 11, orbSize.getD i 0 = 46621575 := by
    simp [Finset.sum_range_succ, orbSize]
  have hsum : 46621575 ≤ ∑ i ∈ Finset.range 11, (F i).card := by
    rw [← hsum0]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
    exact le_ncard_rep11 i (Finset.mem_range.1 hi)
  have hv' : v ∉ (Finset.range 11).biUnion F := by
    intro hm
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 hm
    exact hv i (Finset.mem_range.1 hi) ((Set.Finite.mem_toFinset _).1 hvi)
  have hcard : (insert v ((Finset.range 11).biUnion F)).card =
      (∑ i ∈ Finset.range 11, (F i).card) + 1 := by
    rw [Finset.card_insert_of_notMem hv', hU]
  have hle : (insert v ((Finset.range 11).biUnion F)).card ≤ Nat.card Vt := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_card _
  rw [card_Vt, hcard] at hle
  omega

end CFSG.Sporadic.Co1Patterson
