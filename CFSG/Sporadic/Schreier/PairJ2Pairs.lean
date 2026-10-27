module

public import CFSG.Sporadic.Schreier.PairJ2Order
public import CFSG.Sporadic.Schreier.PairClasses
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Schreier.ImagePairs

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem j2Gen_mem_P (k : ℕ) (hk : k < 2) : j2Gen k ∈ j2P := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem j2Gen_mem (k : ℕ) (hk : k < 2) : j2Gen k ∈ j2Chain.originalSubgroup :=
  j2P_eq_original ▸ j2Gen_mem_P k hk

theorem j2_baseFaithful :
    BaseFaithful j2Chain.originalSubgroup PairJ2.bs := by
  have h := baseFaithful_of_valid j2Chain_valid.1
  rwa [j2Chain_base] at h

theorem j2_bs_lt : ∀ b ∈ PairJ2.bs, b < 315 := by
  decide

theorem j2_bs_eq : PairJ2.bs = j2Chain.base.toList.map Fin.val := j2Chain_base.symm

theorem j2_groups : PairJ2.groups.flatten = List.range j2Chain.baseCount := by
  rw [j2Chain_baseCount]
  rfl

theorem repW_j2wA :
    RepW 315 PairJ2.wA (j2Gen 0) := RepW.single (rep_j2StrongPerm (by norm_num))

theorem repW_j2wB :
    RepW 315 PairJ2.wB (j2Gen 1) := RepW.single (rep_j2StrongPerm (by norm_num))

theorem j2_gens :
    ∀ l < PairJ2.gens.size, Rep 315 PairJ2.gens[l]! (j2Gen l) ∧
      Rep 315 PairJ2.gensInv[l]! (j2Gen l)⁻¹ ∧ j2Gen l ∈ j2Chain.originalSubgroup := by
  intro l hl
  have hl2 : l < 2 := hl
  have hinv := j2CertOK_parts.2.2.2.1 l (by omega)
  have e1 : PairJ2.gens[l]! = j2StrongArrs[l]! := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairJ2.gens]
    · simp [PairJ2.gens]
  have e2 : PairJ2.gensInv[l]! = (rawInvs 315 j2StrongArrs)[l]! := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairJ2.gensInv]
    · simp [PairJ2.gensInv]
  rw [e1, e2]
  exact ⟨rep_j2StrongPerm (by omega), (rep_permOfArr hinv).2, j2Gen_mem l hl2⟩

theorem j2_reps
    (c : List (Array ℕ) × Array (Array ℕ) × Array ℕ × Array ℕ)
    (hc : c ∈ PairJ2.cl) : ∃ x ∈ j2Chain.originalSubgroup, RepW 315 c.1 x := by
  have hab : ∀ t ∈ PairJ2.wA ++ PairJ2.wB, ∃ h ∈ j2Chain.originalSubgroup, Rep 315 t h := by
    intro t ht
    simp only [PairJ2.wA, PairJ2.wB, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨j2Gen 0, j2Gen_mem 0 (by norm_num), rep_j2StrongPerm (by norm_num)⟩
    · exact ⟨j2Gen 1, j2Gen_mem 1 (by norm_num), rep_j2StrongPerm (by norm_num)⟩
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
  refine exists_repW_of_forall fun t ht => hab t ?_
  simp only [PairJ2.reps, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact List.mem_append_left _ ht
  · obtain ⟨l, hl, htl⟩ := List.mem_flatten.1 ht
    rw [(List.mem_replicate.1 hl).2] at htl
    rcases mem_patW htl with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ h

theorem j2_word_orders :
    orderOf (j2Gen 0) = 2 ∧ orderOf (j2Gen 1) = 3 ∧ orderOf (j2Gen 0 * j2Gen 1) = 7 ∧
      orderOf (j2Gen 0 * j2Gen 1 * (j2Gen 0)⁻¹ * (j2Gen 1)⁻¹) = 12 := by
  obtain ⟨h1, h2, h3, h4⟩ := PairJ2.word_orders
  have ha := j2Gen_mem 0 (by norm_num)
  have hb := j2Gen_mem 1 (by norm_num)
  have o1 := (ordB_iff j2_baseFaithful j2_bs_lt repW_j2wA ha (by norm_num)).1 h1
  have o2 := (ordB_iff j2_baseFaithful j2_bs_lt repW_j2wB hb (by norm_num)).1 h2
  have o3 := (ordB_iff j2_baseFaithful j2_bs_lt (repW_patW repW_j2wA repW_j2wB [false, true])
    (patProd_mem _ ha hb _) (by norm_num)).1 h3
  have o4 := (ordB_iff j2_baseFaithful j2_bs_lt (repW_patW repW_j2wA repW_j2wB PairJ2.commPat)
    (patProd_mem _ ha hb _) (by norm_num)).1 h4
  have hrel : PatRel [([false, true], 7), ([false, true, false] ++ List.replicate (3 - 1) true,
      12)] (j2Gen 0) (j2Gen 1) := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact o3
    · exact o4
  obtain ⟨o3', o4'⟩ := (patRel_comm_iff o1 o2 (by norm_num) 7 12).1 hrel
  exact ⟨o1, o2, o3', o4'⟩

theorem j2_card_order
    (m : ℕ) (hm : 0 < m) :
    Nat.card {x : j2Chain.originalSubgroup // orderOf x = m} =
      countW (fun w => ordB PairJ2.bs w m) PairJ2.blocks [] := by
  rw [card_orderOf_coe]
  exact card_eq_countW j2ChainArrays (by norm_num) PairJ2.chain_check.1 j2_groups
    (Pr := fun g => orderOf g = m) fun w g hw hg => ordB_iff j2_baseFaithful j2_bs_lt hw hg hm

theorem j2_card_pairs :
    Nat.card {p : j2Chain.originalSubgroup × j2Chain.originalSubgroup // orderOf p.1 = 2 ∧
      orderOf p.2 = 3 ∧ PatRel PairJ2.conds p.1 p.2} = 1209600 := by
  obtain ⟨h1', h2, h3, h4⟩ := PairJ2.classes
  rw [card_pairs_eq_classTotalNF j2ChainArrays (by norm_num) PairJ2.chain_check.1 j2_bs_eq
    j2_groups (by norm_num) (by norm_num) (by decide) j2_gens PairJ2.cl j2_reps h1' h2 h3
    (h4.trans PairJ2.counts.1.symm)]
  exact PairJ2.total

theorem AT_J2_image_pair_count :
    orderOf (j2Gen 0) = 2 ∧ orderOf (j2Gen 1) = 3 ∧ orderOf (j2Gen 0 * j2Gen 1) = 7 ∧
      orderOf (j2Gen 0 * j2Gen 1 * (j2Gen 0)⁻¹ * (j2Gen 1)⁻¹) = 12 ∧
      Nat.card {x : j2P // orderOf x = 2} = 2835 ∧
      Nat.card {y : j2P // orderOf y = 3} = 17360 ∧
      Nat.card {p : j2P × j2P // orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧
        orderOf (p.1 * p.2) = 7 ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 12} = 1209600 := by
  have hT : Nat.card {p : j2Chain.originalSubgroup × j2Chain.originalSubgroup //
      orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 7 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 12} = 1209600 := by
    rw [← j2_card_pairs]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (patRel_comm_iff h1 h2 (by norm_num) 7 12).2 h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (patRel_comm_iff h1 h2 (by norm_num) 7 12).1 h3⟩
  have h2 := j2_card_order 2 (by norm_num)
  have h3 := j2_card_order 3 (by norm_num)
  rw [PairJ2.counts.1] at h2
  rw [PairJ2.counts.2] at h3
  rw [← j2P_eq_original] at h2 h3 hT
  exact ⟨j2_word_orders.1, j2_word_orders.2.1, j2_word_orders.2.2.1, j2_word_orders.2.2.2, h2, h3,
    hT⟩

@[expose] def j2a : j2P := ⟨j2Gen 0, j2Gen_mem_P 0 (by norm_num)⟩

@[expose] def j2b : j2P := ⟨j2Gen 1, j2Gen_mem_P 1 (by norm_num)⟩

theorem AT_J2_Schreier :
    Nat.card (Outer Blueprint.NativeSporadic.J2) ≤ 2 ∧
      IsMulCommutative (Outer Blueprint.NativeSporadic.J2) ∧
      Group.IsSolvable (Outer Blueprint.NativeSporadic.J2) := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := AT_J2_image_pair_count
  have : IsSimpleGroup Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.2.2
  have : IsSimpleGroup j2P := j2PermEquiv.symm.isSimpleGroup
  have : Finite Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.fam_j2_simplicity.1
  have hgen : Subgroup.closure ({j2a, j2b} : Set j2P) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl _ _
  have ha' : orderOf j2a = 2 := by rw [← Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf j2b = 3 := by rw [← Subgroup.orderOf_coe]; exact hb
  have hab' : orderOf (j2a * j2b) = 7 := by rw [← Subgroup.orderOf_coe]; exact hab
  have hc' : orderOf (j2a * j2b * j2a⁻¹ * j2b⁻¹) = 12 := by rw [← Subgroup.orderOf_coe]; exact hc
  have hP := outer_schreier_of_counts inferInstance hgen ha' hb' hab' hc' (by norm_num) card_j2P
    (by norm_num) hT (k := 2) (by norm_num) (by norm_num)
  have hcard : Nat.card (Outer Blueprint.NativeSporadic.J2) ≤ 2 :=
    outer_card_le_of_equiv hP.1 j2PermEquiv
  exact ⟨hcard, commutative_of_card_le_four (hcard.trans (by norm_num)),
    solvable_of_card_le_four (hcard.trans (by norm_num))⟩

end CFSG.Sporadic.Schreier
