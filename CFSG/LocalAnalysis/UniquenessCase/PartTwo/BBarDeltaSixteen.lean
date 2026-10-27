module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Sixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem bBar_le_of_delta (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (hW4 : Inputs1719.W4Lem4_16b)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hfix : fixV (barSub V₀ V hV.isElemAbelian L) = ⊥)
    (Δ : Set (Subgroup (MulAut (Vtil V₀ V hV.isElemAbelian)))) (k : ℕ)
    (hΔfin : Δ.Finite)
    (hΔ : ∀ H ∈ Δ, H ≤ barSub V₀ V hV.isElemAbelian L ⊔
        barSub V₀ V hV.isElemAbelian D.T ∧ barSub V₀ V hV.isElemAbelian D.T ≤ H)
    (hgen : (⨆ H ∈ Δ, H) = barSub V₀ V hV.isElemAbelian L ⊔
        barSub V₀ V hV.isElemAbelian D.T)
    (hk : fIndexSum Δ ≤ (k : ℕ∞)) :
    bBar L D.M V₀ V hV.isElemAbelian ≤ k := by
  have hV' := hV.isElemAbelian
  have hLM : L ≤ D.M := hL.1.le
  have hLstab : L ≤ stabTil V₀ V :=
    hLM.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have hTstab : D.T ≤ stabTil V₀ V :=
    D.sylowM.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hpow : ∀ w : Vtil V₀ V hV', w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV'
  have hcompM : IsComponentOf (barSub V₀ V hV' L) (Mbar D.M V₀ V hV') :=
    barSub_mem_compBar_of_ne_bot hV hL hL1
  have hLbarM : barSub V₀ V hV' L ≤ Mbar D.M V₀ V hV' := barSub_mono V₀ V hV' hLM
  have hTbarM : barSub V₀ V hV' D.T ≤ Mbar D.M V₀ V hV' :=
    barSub_mono V₀ V hV' D.sylowM.le
  have hNM : Mbar D.M V₀ V hV' ≤ Subgroup.normalizer
      (barSub V₀ V hV' L : Set (MulAut (Vtil V₀ V hV'))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbarM).1
      (barSub_subgroupOf_mbar_normal hV' hLM hMN)
  have hcomp : IsComponentOf (barSub V₀ V hV' L)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) :=
    isComponentOf_sup_of_normal hLbarM hNM hTbarM hcompM
  have hsyl : CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V hV' D.T)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) := by
    have h := S17.isSylowIn_barSub_T_sup hV hLM
    rwa [s16c7_barSub_sup V₀ V hV' hLstab hTstab] at h
  have hfixne : fixV (barSub V₀ V hV' D.T) ≠
      fixV (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) :=
    fixV_ne_fixV_sup hpow hL1 hfix hsyl.isPGroup
  have hbound : bParam (barSub V₀ V hV' L)
      (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) ≤ k :=
    hW4 (Vtil V₀ V hV') hpow (barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T) (barSub V₀ V hV' L)
      (barSub V₀ V hV' D.T) Δ k le_sup_left le_sup_right rfl hcomp hsyl hΔfin
      (fun H hH => ⟨(hΔ H hH).1, (hΔ H hH).2⟩) hgen hk hfixne
  exact bBar_le_of_sup_bound hV hL hN hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
