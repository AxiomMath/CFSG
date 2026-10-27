module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2XInLComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → x ∈ L → x ∈ ⁅Bs, L ⊓ Subgroup.normalizer (Bs : Set G)⁆

theorem ggQTwoXInLDatum_of_comm (h : GGQ2XInLComm) : GGQTwoXInLDatum := by
  refine ggQTwoXInLDatum_of_span ?_
  intro G _ _ p B Bs x L D J hS hxL hpFact y K hnb M
  haveI : Fact p.Prime := hpFact
  have hp2 : p ≠ 2 := hS.1.1.1.2.2.2.2.2.1.2.1
  exact (M.xV_mem_span_iff_mem_commutator hp2).mpr (h G p B Bs x L D J hS hxL)

end CFSG.StandardType

end
