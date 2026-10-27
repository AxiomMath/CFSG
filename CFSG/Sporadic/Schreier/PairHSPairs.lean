
module

public import CFSG.Sporadic.Schreier.PairHSPairsBase

public import CFSG.Sporadic.Schreier.PairHSOrder
public import CFSG.Sporadic.Schreier.PairHSCount
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.Sporadic.Schreier.PairSimple
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairHSCheck
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.Schreier.PairHSFaithfulInputs
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.HS.Data

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.ComponentClassification.OuterAutomorphisms

theorem hs_card_pairs :
    Nat.card {p : hsChain.originalSubgroup × hsChain.originalSubgroup // orderOf p.1 = 2 ∧
      orderOf p.2 = 5 ∧ PatRel PairHS.conds p.1 p.2} = 1064448000 := by
  obtain ⟨h1', h2, h3, h4⟩ := PairHS.classes
  have h4' : (PairHS.cl.map fun c => c.2.1.size).sum =
      countW (fun w => ordB PairHS.bs w 2) (blocksOf 3850 (rawLevels 3850 hsStrongArrs
        PairHS.baseArr) PairHS.groups) [] := by
    rw [h4, ← PairHS.count_two, PairHS.parCount_eq]
    rfl
  rw [card_pairs_eq_classTotalNF hsChainArrays (by norm_num) PairHS.chain_check.1 hs_bs_eq
    hs_groups (by norm_num) (by norm_num) (by decide) hs_gens PairHS.cl hs_reps h1' h2 h3 h4',
    ← PairHS.total]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  rw [PairHS.parCount_eq]
  rfl

theorem AT_HS_image_pair_count :
    orderOf (hsGen 0) = 2 ∧ orderOf (hsGen 1) = 5 ∧ orderOf (hsGen 0 * hsGen 1) = 11 ∧
      orderOf (hsGen 0 * hsGen 1 * (hsGen 0)⁻¹ * (hsGen 1)⁻¹) = 5 ∧
      Nat.card {x : hsP // orderOf x = 2} = 21175 ∧
      Nat.card {y : hsP // orderOf y = 5} = 2010624 ∧
      Nat.card {p : hsP × hsP // orderOf p.1 = 2 ∧ orderOf p.2 = 5 ∧
        orderOf (p.1 * p.2) = 11 ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 5} = 1064448000 := by
  have hT : Nat.card {p : hsChain.originalSubgroup × hsChain.originalSubgroup //
      orderOf p.1 = 2 ∧ orderOf p.2 = 5 ∧ orderOf (p.1 * p.2) = 11 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 5} = 1064448000 := by
    rw [← hs_card_pairs]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (patRel_comm_iff h1 h2 (by norm_num) 11 5).2 h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (patRel_comm_iff h1 h2 (by norm_num) 11 5).1 h3⟩
  have h2 := hs_card_order 2 (by norm_num)
  have h5 := hs_card_order 5 (by norm_num)
  rw [PairHS.count_two] at h2
  rw [PairHS.count_five] at h5
  rw [← hsP_eq_original] at h2 h5 hT
  exact ⟨hs_word_orders.1, hs_word_orders.2.1, hs_word_orders.2.2.1, hs_word_orders.2.2.2, h2, h5,
    hT⟩

theorem AT_HS_Schreier :
    Nat.card (Outer Blueprint.NativeSporadic.HS) ≤ 24 ∧
      Group.IsSolvable (Outer Blueprint.NativeSporadic.HS) := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := AT_HS_image_pair_count
  have : IsSimpleGroup hsP :=
    isSimpleGroup_of_mulEquiv_perm CFSG.Sporadic.HS.fam_hs_simplicity.2.2 hsPermEquiv
  have : Finite Blueprint.NativeSporadic.HS := CFSG.Sporadic.HS.fam_hs_simplicity.1
  have hgen : Subgroup.closure ({hsa0, hsa1} : Set hsP) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl _ _
  have ha' : orderOf hsa0 = 2 := by rw [← Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf hsa1 = 5 := by rw [← Subgroup.orderOf_coe]; exact hb
  have hab' : orderOf (hsa0 * hsa1) = 11 := by rw [← Subgroup.orderOf_coe]; exact hab
  have hc' : orderOf (hsa0 * hsa1 * hsa0⁻¹ * hsa1⁻¹) = 5 := by
    rw [← Subgroup.orderOf_coe]; exact hc
  have hP := outer_card_le_of_counts inferInstance hgen ha' hb' hab' hc' (by norm_num) card_hsP
    (by norm_num) hT (k := 24) (by norm_num)
  have hcard : Nat.card (Outer Blueprint.NativeSporadic.HS) ≤ 24 :=
    outer_card_le_of_equiv hP hsPermEquiv
  exact ⟨hcard, CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)⟩

end CFSG.Sporadic.Schreier
