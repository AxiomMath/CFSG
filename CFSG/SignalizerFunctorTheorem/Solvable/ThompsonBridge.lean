module

public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonSubgroupTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.AmbientSolvableZJ
public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore
import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonCanonical
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonCanonical

public section

namespace CFSG.SignalizerFunctorTheorem.Solvable

open CFSG.SignalizerFunctor.Helpers CFSG.RankThreeEvenClassification.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem maximumOrderAbelian_iff_mem_family (H : Subgroup G) :
    MaximumOrderAbelian H ↔ H ∈ maximumOrderAbelianFamily G := by
  rw [maximumOrderAbelian_iff_mem_maxOrderAbelianFamily,
    maximum_order_abelian_family_eq_maxOrderAbelianFamily]

theorem thompsonOrderSubgroup_eq_orderThompsonSubgroup :
    thompsonOrderSubgroup G = orderThompsonSubgroup G := by
  rw [thompsonOrderSubgroup_eq_orderThompson, order_thompson_subgroup_eq_orderThompson]

theorem thompsonOrderCenter_eq_orderThompsonCenter :
    thompsonOrderCenter G = orderThompsonCenter G := by
  rw [thompsonOrderCenter_eq_orderZJ, order_thompson_center_eq_orderZJ]

theorem thompsonCenterOf_eq_embeddedOrderThompsonCenter (T : Subgroup G) :
    thompsonCenterOf T = embeddedOrderThompsonCenter T := by
  show (CFSG.orderZJ T).map T.subtype = (orderThompsonCenter T).map T.subtype
  rw [order_thompson_center_eq_orderZJ]

omit [Finite G] in
theorem primeComplementCore_eq_primeSetCore {q : ℕ} (hq : q.Prime) :
    primeComplementCore G q = primeSetCore (GroupType := G) ({q}ᶜ) := by
  unfold primeComplementCore primeSetCore
  rw [sSup_eq_iSup']
  apply le_antisymm
  · refine iSup_le fun N => le_iSup₂_of_le N.val ⟨N.property.1, ?_⟩ le_rfl
    exact (prime_supported_complement_singleton_iff_coprime q hq _).mpr
      ((Nat.Prime.coprime_iff_not_dvd hq).mpr N.property.2)
  · refine iSup₂_le fun N hN => le_iSup_of_le ⟨N, hN.1, ?_⟩ le_rfl
    exact (Nat.Prime.coprime_iff_not_dvd hq).mp
      ((prime_supported_complement_singleton_iff_coprime q hq _).mp hN.2)

theorem solvable_zj_factorization {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (U : Subgroup G)
    [Group.IsSolvable U] (T : Sylow q U) :
    (primeSetCore (GroupType := U) ({q}ᶜ)).map U.subtype ⊔
      (U ⊓ Subgroup.normalizer
        (embeddedOrderThompsonCenter ((T : Subgroup U).map U.subtype) : Set G)) = U := by
  rw [← primeComplementCore_eq_primeSetCore hq,
    ← thompsonCenterOf_eq_embeddedOrderThompsonCenter]
  exact ambient_solvable_zj_normalizer_factorization_sup q hq hq5 U T

end CFSG.SignalizerFunctorTheorem.Solvable
