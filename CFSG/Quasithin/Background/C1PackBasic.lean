module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Background.A4
public import CFSG.Quasithin.Background.C1GNA7Base

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isShort2_eq_oTwoUpper {L : Subgroup G} (hL : IsShort2 L) : L = oTwoUpper L := by
  have hN : ((oTwoUpper L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L)
  have h2 : IsPGroup 2 (↥L ⧸ (oTwoUpper L).subgroupOf L) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper L x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp (hL.1 _ h2)) (oTwoUpper_le L)

theorem isBlock2_normal_sup_pCore {H B : Subgroup G} (hB : IsBlock2 H B) :
    B = oTwoUpper (B ⊔ pCoreOf 2 H) ∧ (B.subgroupOf (B ⊔ pCoreOf 2 H)).Normal := by
  have hBH : B ≤ H := hB.2.1
  have hBN : B ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hBH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
  have hprod : ((pCoreOf 2 H : Subgroup G) : Set G) * (B : Set G) =
      (B : Set G) * (pCoreOf 2 H : Subgroup G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 H) B hBN, sup_comm,
      Subgroup.coe_mul_of_left_le_normalizer_right B (pCoreOf 2 H) hBN]
  exact a4_2_2 (isShort2_eq_oTwoUpper hB.1) (C1GN.isSubnormal_of_isBlock2 hB)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H) hprod

theorem blockQ_eq_inf_pCoreOf {H B : Subgroup G} (hB : IsBlock2 H B) :
    blockQ B = B ⊓ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBH : B ≤ H := hB.2.1
  apply le_antisymm
  · exact le_inf (C1.blockQ_le B)
      (A4.pCoreOf_le_of_subnormal 2 (C1GN.isSubnormal_of_isBlock2 hB))
  · refine C1.le_pCoreOf_of_normalized inf_le_left ?_
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).to_le inf_le_right)
    intro g hg
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer hg)
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H (hBH hg))

end CFSG.Quasithin.C1Pack
