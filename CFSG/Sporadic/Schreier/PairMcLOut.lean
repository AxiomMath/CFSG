module

public import CFSG.Sporadic.Schreier.PairMcLPairs
public import CFSG.Sporadic.Schreier.PairMcLTotal2
public import CFSG.Sporadic.Schreier.PairOuterPat

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem mcl_card_pairs2 :
    Nat.card {p : mclChain.originalSubgroup × mclChain.originalSubgroup // orderOf p.1 = 2 ∧
      orderOf p.2 = 5 ∧ PatRel PairMcL.conds2 p.1 p.2} = 1796256000 := by
  obtain ⟨h1', h2, h3, h4⟩ := PairMcL.classes
  have h4' : (PairMcL.cl.map fun c => c.2.1.size).sum =
      countW (fun w => ordB PairMcL.bs w 2) (blocksOf 275 (rawLevels 275 mclStrongArrs
        PairMcL.baseArr) PairMcL.groups) [] := by
    rw [h4, ← PairMcL.count_two, countOrd_eq]
    rfl
  rw [card_pairs_eq_classTotalNF mclChainArrays (by norm_num) PairMcL.chain_check.1 mcl_bs_eq
    mcl_groups (conds := PairMcL.conds2) (by norm_num) (by norm_num) (by decide) mcl_gens
    PairMcL.cl mcl_reps h1' h2 h3 h4', ← PairMcL.total2]
  congr 1

theorem mcl_patRel2 :
    PatRel PairMcL.conds2 (mclGen 0) (mclGen 1) := by
  obtain ⟨-, -, w3, w4⟩ := PairMcL.word_orders
  obtain ⟨w5, w6, w7⟩ := PairMcL.word_orders2
  have ha := mclGen_mem 0 (by norm_num)
  have hb := mclGen_mem 1 (by norm_num)
  have hord : ∀ pat : List Bool, ∀ m : ℕ, 0 < m →
      ordB PairMcL.bs (patW PairMcL.wA PairMcL.wB pat) m = true →
        orderOf (pat.map fun b => if b then mclGen 1 else mclGen 0).prod = m :=
    fun pat m hm h => (ordB_iff mcl_baseFaithful mcl_bs_lt (repW_patW repW_mclwA repW_mclwB pat)
      (patProd_mem _ ha hb pat) hm).1 h
  intro c hc
  rw [show PairMcL.conds2 = [([false, true], 11), (PairMcL.commPat, 5),
    ([false, true, true], 12), ([false, true, false, true, true], 14), (PairMcL.pat10, 10)]
    from rfl] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact hord _ _ (by norm_num) w3
  · exact hord _ _ (by norm_num) w4
  · exact hord _ _ (by norm_num) w5
  · exact hord _ _ (by norm_num) w6
  · exact hord _ _ (by norm_num) w7

theorem McL_outer_card_le_two :
    Nat.card (Outer Blueprint.NativeSporadic.McL) ≤ 2 ∧
      IsMulCommutative (Outer Blueprint.NativeSporadic.McL) ∧
      Group.IsSolvable (Outer Blueprint.NativeSporadic.McL) := by
  obtain ⟨ha, hb, -, hc, -, -, -⟩ := AT_McL_image_pair_count
  have : IsSimpleGroup mclP :=
    isSimpleGroup_of_mulEquiv_perm CFSG.Sporadic.McL.fam_mcl_simplicity.2.2 mclPermEquiv
  have : Finite Blueprint.NativeSporadic.McL := CFSG.Sporadic.McL.fam_mcl_simplicity.1
  have hgen : Subgroup.closure ({mcla0, mcla1} : Set mclP) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl _ _
  have ha' : orderOf mcla0 = 2 := by rw [← Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf mcla1 = 5 := by rw [← Subgroup.orderOf_coe]; exact hb
  have hcomm : mcla0 * mcla1 ≠ mcla1 * mcla0 := by
    refine mul_ne_mul_of_orderOf_commutator (s := 5) ?_ (by norm_num)
    rw [← Subgroup.orderOf_coe]
    exact hc
  have hrel : PatRel PairMcL.conds2 mcla0 mcla1 :=
    (patRel_coe PairMcL.conds2 mcla0 mcla1).1 mcl_patRel2
  have hT : Nat.card {p : mclP × mclP // orderOf p.1 = orderOf mcla0 ∧
      orderOf p.2 = orderOf mcla1 ∧ PatRel PairMcL.conds2 p.1 p.2} = 1796256000 := by
    have h := mcl_card_pairs2
    rw [← mclP_eq_original] at h
    rw [ha', hb']
    exact h
  have hP : Nat.card (Outer mclP) ≤ 2 :=
    outer_card_le_of_patCounts inferInstance hgen hcomm PairMcL.conds2 hrel card_mclP
      (by norm_num) hT (k := 2) (by norm_num)
  have hcard : Nat.card (Outer Blueprint.NativeSporadic.McL) ≤ 2 :=
    outer_card_le_of_equiv hP mclPermEquiv
  exact ⟨hcard, commutative_of_card_le_four (hcard.trans (by norm_num)),
    solvable_of_card_le_four (hcard.trans (by norm_num))⟩

end CFSG.Sporadic.Schreier
