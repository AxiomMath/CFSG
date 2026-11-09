module

public import CFSG.Sporadic.Schreier.PairMcLOrder
public import CFSG.Sporadic.Schreier.PairMcLCountTwo
public import CFSG.Sporadic.Schreier.PairMcLCountFive
public import CFSG.Sporadic.Schreier.PairMcLTotal
public import CFSG.Sporadic.Schreier.PairCounts
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.Sporadic.Schreier.PairSimple
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Sporadic.Schreier.PairOuterPat
public import CFSG.Sporadic.Schreier.PairOneClass

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.ComponentClassification.OuterAutomorphisms

theorem mcl_bs_eq : PairMcL.bs = mclChain.base.toList.map Fin.val := mclChain_base.symm

theorem mcl_groups : PairMcL.groups.flatten = List.range mclChain.baseCount := by
  rw [mclChain_baseCount]
  rfl

theorem mcl_gens :
    ∀ l < PairMcL.gens.size, Rep 275 PairMcL.gens[l]! (mclGen l) ∧
      Rep 275 PairMcL.gensInv[l]! (mclGen l)⁻¹ ∧ mclGen l ∈ mclChain.originalSubgroup := by
  intro l hl
  have hl2 : l < 2 := hl
  have hinv := (mclCertOK_parts.2.2.1 l (by omega)).2
  have e1 : PairMcL.gens[l]! = mclStrongArrs[l]! := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairMcL.gens]
    · simp [PairMcL.gens]
  have e2 : PairMcL.gensInv[l]! = (rawInvs 275 mclStrongArrs)[l]! := by
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp [PairMcL.gensInv]
    · simp [PairMcL.gensInv]
  rw [e1, e2]
  exact ⟨rep_mclGen (by omega), (rep_permOfArr hinv).2, mclGen_mem l hl2⟩

theorem mcl_reps
    (c : List (Array ℕ) × Array (Array ℕ) × Array ℕ × Array ℕ)
    (hc : c ∈ PairMcL.cl) : ∃ x ∈ mclChain.originalSubgroup, RepW 275 c.1 x := by
  simp only [PairMcL.cl, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  subst hc
  exact ⟨mclGen 0, mclGen_mem 0 (by norm_num), repW_mclwA⟩

theorem mcl_card_order
    (m : ℕ) (hm : 0 < m) :
    Nat.card {x : mclChain.originalSubgroup // orderOf x = m} =
      countOrd PairMcL.bs m PairMcL.blocks := by
  rw [card_orderOf_coe, countOrd_eq]
  exact card_eq_countW mclChainArrays (by norm_num) PairMcL.chain_check.1 mcl_groups
    (Pr := fun g => orderOf g = m) fun w g hw hg => ordB_iff mcl_baseFaithful mcl_bs_lt hw hg hm

theorem mcl_card_pairsW {conds : List (List Bool × ℕ)} (hconds : ∀ c ∈ conds, 0 < c.2) :
    Nat.card {p : mclChain.originalSubgroup × mclChain.originalSubgroup // orderOf p.1 = 2 ∧
      orderOf p.2 = 5 ∧ PatRel conds p.1 p.2} =
      22275 * countPair PairMcL.bs 5 PairMcL.wA conds PairMcL.blocks := by
  set H := mclChain.originalSubgroup
  have hm0 := mclGen_mem 0 (by norm_num)
  set x₀ : H := ⟨mclGen 0, hm0⟩
  have hx₀ : orderOf x₀ = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact mcl_word_orders.1
  have hR : ∀ c x y : H, (orderOf (c * y * c⁻¹) = 5 ∧ PatRel conds (c * x * c⁻¹) (c * y * c⁻¹)) ↔
      (orderOf y = 5 ∧ PatRel conds x y) := fun c x y => by
    rw [patRel_conj, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have h2 : Nat.card {x : H // orderOf x = 2} = 22275 := by
    rw [mcl_card_order 2 (by norm_num), PairMcL.count_two]
  have hcl : Nat.card {x : H // IsConj x₀ x} = 22275 := by
    have key : ∀ (K : Subgroup (Equiv.Perm (Fin 275))), K = mclP → ∀ hm : mclGen 0 ∈ K,
        Nat.card {x : K // IsConj (⟨mclGen 0, hm⟩ : K) x} = 22275 := by
      rintro K rfl hm
      exact PairMcL.card_class
    exact key H mclP_eq_original.symm hm0
  have hpart : Nat.card {y : H // orderOf y = 5 ∧ PatRel conds x₀ y} =
      countPair PairMcL.bs 5 PairMcL.wA conds PairMcL.blocks := by
    have e : ∀ y : H, (orderOf y = 5 ∧ PatRel conds x₀ y) ↔
        (orderOf (y : Equiv.Perm (Fin 275)) = 5 ∧ PatRel conds (mclGen 0) y) := fun y => by
      rw [Subgroup.orderOf_coe, ← patRel_coe]
    rw [Nat.card_congr (Equiv.subtypeEquivRight e)]
    refine card_eq_countW mclChainArrays (by norm_num) PairMcL.chain_check.1 mcl_groups
      (Pr := fun g => orderOf g = 5 ∧ PatRel conds (mclGen 0) g) fun w g hw hg => ?_
    change (ordB PairMcL.bs w 5 && condsOK PairMcL.bs PairMcL.wA w conds) = true ↔ _
    rw [Bool.and_eq_true, ordB_iff mcl_baseFaithful mcl_bs_lt hw hg (by norm_num),
      condsOK_iff mcl_baseFaithful mcl_bs_lt repW_mclwA hw hm0 hg hconds]
    rfl
  rw [card_pairs_of_oneClass x₀ hx₀ (fun x y => orderOf y = 5 ∧ PatRel conds x y) hR
    (by rw [h2, hcl]), h2, hpart]

theorem mcl_card_pairs :
    Nat.card {p : mclChain.originalSubgroup × mclChain.originalSubgroup // orderOf p.1 = 2 ∧
      orderOf p.2 = 5 ∧ PatRel PairMcL.conds p.1 p.2} = 48498912000 := by
  rw [mcl_card_pairsW (by decide), PairMcL.total]

theorem AT_McL_image_pair_count :
    orderOf (mclGen 0) = 2 ∧ orderOf (mclGen 1) = 5 ∧ orderOf (mclGen 0 * mclGen 1) = 11 ∧
      orderOf (mclGen 0 * mclGen 1 * (mclGen 0)⁻¹ * (mclGen 1)⁻¹) = 5 ∧
      Nat.card {x : mclP // orderOf x = 2} = 22275 ∧
      Nat.card {y : mclP // orderOf y = 5} = 37122624 ∧
      Nat.card {p : mclP × mclP // orderOf p.1 = 2 ∧ orderOf p.2 = 5 ∧
        orderOf (p.1 * p.2) = 11 ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 5} = 48498912000 := by
  have hT : Nat.card {p : mclChain.originalSubgroup × mclChain.originalSubgroup //
      orderOf p.1 = 2 ∧ orderOf p.2 = 5 ∧ orderOf (p.1 * p.2) = 11 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 5} = 48498912000 := by
    rw [← mcl_card_pairs]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (patRel_comm_iff h1 h2 (by norm_num) 11 5).2 h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (patRel_comm_iff h1 h2 (by norm_num) 11 5).1 h3⟩
  have h2 := mcl_card_order 2 (by norm_num)
  have h5 := mcl_card_order 5 (by norm_num)
  rw [PairMcL.count_two] at h2
  rw [PairMcL.count_five] at h5
  rw [← mclP_eq_original] at h2 h5 hT
  exact ⟨mcl_word_orders.1, mcl_word_orders.2.1, mcl_word_orders.2.2.1, mcl_word_orders.2.2.2,
    h2, h5, hT⟩

@[expose] def mcla0 : mclP := ⟨mclGen 0, mclGen_mem_P 0 (by norm_num)⟩

@[expose] def mcla1 : mclP := ⟨mclGen 1, mclGen_mem_P 1 (by norm_num)⟩

theorem AT_McL_Schreier :
    Nat.card (Outer Blueprint.NativeSporadic.McL) ≤ 54 ∧
      Group.IsSolvable (Outer Blueprint.NativeSporadic.McL) := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := AT_McL_image_pair_count
  have : IsSimpleGroup mclP :=
    isSimpleGroup_of_mulEquiv_perm CFSG.Sporadic.McL.fam_mcl_simplicity.2.2 mclPermEquiv
  have : Finite Blueprint.NativeSporadic.McL := CFSG.Sporadic.McL.fam_mcl_simplicity.1
  have hgen : Subgroup.closure ({mcla0, mcla1} : Set mclP) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl _ _
  have ha' : orderOf mcla0 = 2 := by rw [← Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf mcla1 = 5 := by rw [← Subgroup.orderOf_coe]; exact hb
  have hab' : orderOf (mcla0 * mcla1) = 11 := by rw [← Subgroup.orderOf_coe]; exact hab
  have hc' : orderOf (mcla0 * mcla1 * mcla0⁻¹ * mcla1⁻¹) = 5 := by
    rw [← Subgroup.orderOf_coe]; exact hc
  have hP := outer_card_le_of_counts inferInstance hgen ha' hb' hab' hc' (by norm_num) card_mclP
    (by norm_num) hT (k := 54) (by norm_num)
  have hcard : Nat.card (Outer Blueprint.NativeSporadic.McL) ≤ 54 :=
    outer_card_le_of_equiv hP mclPermEquiv
  exact ⟨hcard, CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)⟩

end CFSG.Sporadic.Schreier
