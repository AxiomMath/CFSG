module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem sup_pCoreOf_isSubnormal {L M : Subgroup G} (h : CFSG.Open.IsSubnormal L M) :
    CFSG.Open.IsSubnormal (L ⊔ pCoreOf 2 M) M := by
  have hLM : L ≤ M := CFSG.Open.IsSubnormal.le h
  have hPM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  rw [CFSG.Quasithin.isSubnormal_iff_subgroupOf (sup_le hLM hPM),
    Subgroup.subgroupOf_sup hLM hPM]
  exact CFSG.GroupTheory.isSubnormal_sup
    ((CFSG.Quasithin.isSubnormal_iff_subgroupOf hLM).1 h)
    (Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)).isSubnormal

theorem pCoreOf_sup_pCoreOf_of_isSubnormal {L M : Subgroup G}
    (h : CFSG.Open.IsSubnormal L M) :
    pCoreOf 2 (L ⊔ pCoreOf 2 M) = pCoreOf 2 M := by
  refine le_antisymm (CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal
    (sup_pCoreOf_isSubnormal h)) ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
    ((sup_le (CFSG.Open.IsSubnormal.le h) (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)

theorem subgroupOf_pCoreOf_sup_eq_pCore_of_isSubnormal {L M : Subgroup G}
    (h : CFSG.Open.IsSubnormal L M) :
    (pCoreOf 2 M).subgroupOf (L ⊔ pCoreOf 2 M) =
      CFSG.pCore 2 ↥(L ⊔ pCoreOf 2 M) := by
  apply (Subgroup.map_subtype_inj (H := L ⊔ pCoreOf 2 M)).mp
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right,
    show (CFSG.pCore 2 ↥(L ⊔ pCoreOf 2 M)).map (L ⊔ pCoreOf 2 M).subtype =
      pCoreOf 2 (L ⊔ pCoreOf 2 M) from rfl]
  exact (pCoreOf_sup_pCoreOf_of_isSubnormal h).symm

theorem bar2_sup_pCoreOf_mulEquiv_of_mem_calC {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    Nonempty (Bar2 (L ⊔ pCoreOf 2 D.M) ≃* Bar2 L) := by
  have hLN : L ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    (CFSG.Open.IsSubnormal.le hL.1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hKM : L ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le (CFSG.Open.IsSubnormal.le hL.1) (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hKN : L ⊔ pCoreOf 2 D.M ≤
      Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    hKM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hNL : ((pCoreOf 2 D.M).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLN
  have hNK : ((pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKN
  let e1 := QuotientGroup.quotientInfEquivProdNormalizerQuotient L (pCoreOf 2 D.M) hLN
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
      (subgroupOf_pCoreOf_sup_eq_pCore_of_isSubnormal hL.1)).symm.trans
    (e1.symm.trans
      (QuotientGroup.quotientMulEquivOfEq
        (S17.subgroupOf_pCoreOf_eq_pCore_of_mem_calC hL)))⟩

theorem isComponentModO2_sup_pCoreOf_of_mem_calC {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    F12.IsComponentModO2 D.M (L ⊔ pCoreOf 2 D.M) := by
  have hKM : L ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le (CFSG.Open.IsSubnormal.le hL.1) (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hKsn : CFSG.Open.IsSubnormal (L ⊔ pCoreOf 2 D.M) D.M := sup_pCoreOf_isSubnormal hL.1
  refine ⟨le_sup_right, hKM, hKsn, ?_⟩
  have hAn : ((pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      (hKM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
  refine ⟨hAn, ?_⟩
  obtain ⟨e⟩ := bar2_sup_pCoreOf_mulEquiv_of_mem_calC hL
  exact CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.isQuasisimple_of_open
    (hL.2.2.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq
        (subgroupOf_pCoreOf_sup_eq_pCore_of_isSubnormal hL.1)).trans e))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
