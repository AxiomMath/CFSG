
module

public import CFSG.Sporadic.Schreier.PairJ3PairsBase

public import CFSG.Sporadic.Schreier.PairJ3Order
public import CFSG.Sporadic.Schreier.PairJ3Count
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.PairOuter
public import CFSG.Sporadic.Schreier.PairSimple
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairJ3Check
public import Certificates.Data.CFSGNative.PairSchreier.Preds
public meta import CFSG.Sporadic.Schreier.PairJ3Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Preds
public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.J3.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.J3.Data

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.ComponentClassification.OuterAutomorphisms

theorem j3_card_pairs :
    Nat.card {p : j3Chain.originalSubgroup × j3Chain.originalSubgroup // orderOf p.1 = 2 ∧
      orderOf p.2 = 3 ∧ PatRel PairJ3.conds p.1 p.2} = 301397760 := by
  obtain ⟨h1', h2, h3, h4⟩ := PairJ3.classes
  have h4' : (PairJ3.cl.map fun c => c.2.1.size).sum =
      countW (fun w => ordB PairJ3.bs w 2) (blocksOf 6156 (rawLevels 6156 j3StrongArrs
        PairJ3.baseArr) PairJ3.groups) [] := by
    rw [h4, ← PairJ3.count_two, PairJ3.parCount_eq]
    rfl
  rw [card_pairs_eq_classTotalNF j3ChainArrays (by norm_num) PairJ3.chain_check.1 j3_bs_eq
    j3_groups (by norm_num) (by norm_num) (by decide) j3_gens PairJ3.cl j3_reps h1' h2 h3 h4',
    ← PairJ3.total]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  rw [PairJ3.parCount_eq]
  rfl

theorem AT_J3_image_pair_count :
    orderOf (j3Gen 0) = 2 ∧ orderOf (j3Gen 1) = 3 ∧ orderOf (j3Gen 0 * j3Gen 1) = 19 ∧
      orderOf (j3Gen 0 * j3Gen 1 * (j3Gen 0)⁻¹ * (j3Gen 1)⁻¹) = 9 ∧
      Nat.card {x : j3P // orderOf x = 2} = 26163 ∧
      Nat.card {y : j3P // orderOf y = 3} = 253232 ∧
      Nat.card {p : j3P × j3P // orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧
        orderOf (p.1 * p.2) = 19 ∧ orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 9} = 301397760 := by
  have hT : Nat.card {p : j3Chain.originalSubgroup × j3Chain.originalSubgroup //
      orderOf p.1 = 2 ∧ orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 19 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 9} = 301397760 := by
    rw [← j3_card_pairs]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (patRel_comm_iff h1 h2 (by norm_num) 19 9).2 h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (patRel_comm_iff h1 h2 (by norm_num) 19 9).1 h3⟩
  have h2 := j3_card_order 2 (by norm_num)
  have h3 := j3_card_order 3 (by norm_num)
  rw [PairJ3.count_two] at h2
  rw [PairJ3.count_three] at h3
  rw [← j3P_eq_original] at h2 h3 hT
  exact ⟨j3_word_orders.1, j3_word_orders.2.1, j3_word_orders.2.2.1, j3_word_orders.2.2.2, h2, h3,
    hT⟩

theorem AT_J3_Schreier :
    Nat.card (Outer Blueprint.NativeSporadic.J3) ≤ 6 ∧
      Group.IsSolvable (Outer Blueprint.NativeSporadic.J3) := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := AT_J3_image_pair_count
  have : IsSimpleGroup j3P :=
    isSimpleGroup_of_mulEquiv_perm CFSG.Sporadic.J3.fam_j3_simplicity.2.2 j3PermEquiv
  have : Finite Blueprint.NativeSporadic.J3 := CFSG.Sporadic.J3.fam_j3_simplicity.1
  have hgen : Subgroup.closure ({j3a, j3b} : Set j3P) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl _ _
  have ha' : orderOf j3a = 2 := by rw [← Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf j3b = 3 := by rw [← Subgroup.orderOf_coe]; exact hb
  have hab' : orderOf (j3a * j3b) = 19 := by rw [← Subgroup.orderOf_coe]; exact hab
  have hc' : orderOf (j3a * j3b * j3a⁻¹ * j3b⁻¹) = 9 := by rw [← Subgroup.orderOf_coe]; exact hc
  have hP := outer_card_le_of_counts inferInstance hgen ha' hb' hab' hc' (by norm_num) card_j3P
    (by norm_num) hT (k := 6) (by norm_num)
  have hcard : Nat.card (Outer Blueprint.NativeSporadic.J3) ≤ 6 :=
    outer_card_le_of_equiv hP j3PermEquiv
  exact ⟨hcard, CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega)⟩

end CFSG.Sporadic.Schreier
