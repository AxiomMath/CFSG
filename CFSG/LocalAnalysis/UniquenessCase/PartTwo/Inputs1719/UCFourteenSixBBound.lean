module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFourBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormalHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_barSub_T_sup_of_le_stabTil {D : Data G} {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hLM : L ≤ D.M) (hLT : L ⊔ D.T ≤ stabTil V₀ V) :
    CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V hV D.T) (barSub V₀ V hV (L ⊔ D.T)) := by
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf (stabTil V₀ V))
      ((L ⊔ D.T).subgroupOf (stabTil V₀ V)) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (stabTil V₀ V),
      Subgroup.map_subgroupOf_eq_of_le (le_sup_right.trans hLT),
      Subgroup.map_subgroupOf_eq_of_le hLT]
    exact CFSG.ABGLocalTools.isSylowOf_iff.2 (S17.isSylowIn_T_sup hLM)
  exact CFSG.ABGLocalTools.isSylowOf_iff.1
    (s16c7_isSylowOf_map h1 (actTil V₀ V hV))

theorem fixV_barSub_T_ne_fixV_barSub_sup {D : Data G} {V Y : Subgroup G}
    (hV : IsElemAbelian 2 V) (hYV : Y ≤ stabTil ⊥ V) (hTV : D.T ≤ stabTil ⊥ V)
    {v : G} (hvV : v ∈ V) (hvT : v ∈ Subgroup.centralizer (D.T : Set G))
    (hvY : v ∉ Subgroup.centralizer (Y : Set G)) :
    fixV (barSub ⊥ V hV D.T) ≠ fixV (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T) := by
  have hqT : mkTil ⊥ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈ fixV (barSub ⊥ V hV D.T) := by
    rw [fixV_barSub_eq_imgTil_centralizer hV hTV, mem_imgTil]
    exact ⟨IntMod.mk hV ⟨v, hvV⟩, ⟨hvV, hvT⟩, rfl⟩
  have hqY : mkTil ⊥ V hV (IntMod.mk hV ⟨v, hvV⟩) ∉
      fixV (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T) := by
    rw [← s16c7_barSub_sup ⊥ V hV hYV hTV,
      fixV_barSub_eq_imgTil_centralizer hV (sup_le hYV hTV), mem_imgTil]
    rintro ⟨x, hx, hxq⟩
    obtain ⟨-, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxval : x.val = v := by
      have h := (TwelveShort.mkTilEquiv V hV).injective hxq
      rw [h]
      rfl
    rw [hxval] at hxC
    refine hvY ?_
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro y hy
    exact hxC y (Subgroup.mem_sup_left hy)
  intro heq
  exact hqY (heq ▸ hqT)

theorem bBar_le_of_not_inf_centralizer_le
    (h416 : W4Lem4_16) {D : Data G} {Y V : Subgroup G} (hV : IsElemAbelian 2 V) {n : ℕ}
    (hMV : D.M ≤ normalizer (V : Set G)) (hY : Y ∈ calC D.M)
    (hMY : D.M ≤ normalizer (Y : Set G)) (h2 : barSub ⊥ V hV (pCoreOf 2 Y) = ⊥)
    (hY1 : barSub ⊥ V hV Y ≠ ⊥) (hSU : IsSU3 ↥(barSub ⊥ V hV Y) n)
    (hodd : Odd (Nat.card (Subgroup.center ↥(barSub ⊥ V hV Y))))
    (hT : ¬ V ⊓ centralizer (D.T : Set G) ≤ centralizer (Y : Set G)) :
    bBar Y D.M ⊥ V hV ≤ n := by
  classical
  have hMstab : D.M ≤ stabTil ⊥ V :=
    le_stabTil (V₀ := ⊥) hMV (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hYstab : Y ≤ stabTil ⊥ V := hY.1.le.trans hMstab
  have hTstab : D.T ≤ stabTil ⊥ V := D.sylowM.le.trans hMstab
  have hLTle : barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T ≤ Mbar D.M ⊥ V hV :=
    sup_le (barSub_mono ⊥ V hV hY.1.le) (barSub_mono ⊥ V hV D.sylowM.le)
  have hNbar : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer (barSub ⊥ V hV Y : Set (MulAut (Vtil ⊥ V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (barSub_mono ⊥ V hV hY.1.le)).1
      (barSub_subgroupOf_mbar_normal hV hY.1.le hMY)
  have hqbar : CFSG.Open.IsQuasisimple ↥(barSub ⊥ V hV Y) :=
    TwelveTwentyThree.isQuasisimple_barSub hV hYstab hY.2.2 h2 hY1
  have hcompM : IsComponentOf (barSub ⊥ V hV Y) (Mbar D.M ⊥ V hV) :=
    ⟨barSub_mono ⊥ V hV hY.1.le, TwelveTwentyThree.isSubnormal_barSub hV hY.1, hqbar⟩
  have hcomp : IsComponentOf (barSub ⊥ V hV Y)
      (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T) :=
    isComponentOf_sup_of_normal (Y := Mbar D.M ⊥ V hV) (barSub_mono ⊥ V hV hY.1.le)
      hNbar (barSub_mono ⊥ V hV D.sylowM.le) hcompM
  have hsyl : CFSG.Quasithin.IsSylowIn 2 (barSub ⊥ V hV D.T)
      (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T) := by
    have h := isSylowIn_barSub_T_sup_of_le_stabTil (V₀ := ⊥) hV hY.1.le
      (sup_le hYstab hTstab)
    rwa [s16c7_barSub_sup ⊥ V hV hYstab hTstab] at h
  have hsylMbar : CFSG.Quasithin.IsSylowIn 2 (barSub ⊥ V hV D.T) (Mbar D.M ⊥ V hV) :=
    s16c1_barSub_sylow hMstab ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM)
  have hperf : ⁅barSub ⊥ V hV Y, barSub ⊥ V hV Y⁆ = barSub ⊥ V hV Y := by
    rw [← Subgroup.map_subtype_commutator, hqbar.1, Subgroup.map_top, Subgroup.range_subtype]
  have hbar2 : IsSU3 (UC22.Bar2 (barSub ⊥ V hV Y)) n :=
    S17.isSU3_bar2_of_isSU3 hSU hodd
  have hnorm : ((barSub ⊥ V hV Y).subgroupOf
      (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (hLTle.trans hNbar)
  have hInY : CFSG.LocalAnalysis.WeakClosure81.InFSq n
      (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T) :=
    k_U3IndexNormal_holds (X := MulAut (Vtil ⊥ V hV)) (barSub ⊥ V hV Y)
      (barSub ⊥ V hV D.T) (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T) n
      le_sup_left hnorm hperf hbar2.1 hbar2 hsyl rfl
  have hsum : fIndexSum ({(barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T)} :
      Set (Subgroup (MulAut (Vtil ⊥ V hV)))) ≤ (n : ℕ∞) := by
    rw [fIndexSum, finsum_mem_singleton]
    exact fIndex_le_iff.mpr hInY
  have hfix : fixV (barSub ⊥ V hV D.T) ≠
      fixV (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T) := by
    obtain ⟨v, hv, hvY⟩ := Set.not_subset.1 hT
    obtain ⟨hvV, hvT⟩ := Subgroup.mem_inf.mp hv
    exact fixV_barSub_T_ne_fixV_barSub_sup hV hYstab hTstab hvV hvT hvY
  have hbound : bParam (barSub ⊥ V hV Y)
      (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T) ≤ n :=
    (w4Lem4_16b_of_w4Lem4_16 h416) (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV)
      (barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T) (barSub ⊥ V hV Y) (barSub ⊥ V hV D.T)
      {(barSub ⊥ V hV Y ⊔ barSub ⊥ V hV D.T)} n le_sup_left le_sup_right rfl hcomp hsyl
      (Set.finite_singleton _) (by rintro H rfl; exact ⟨le_rfl, le_sup_right⟩) (by simp) hsum
      hfix
  exact (bParam_le_of_normal (barSub_mono ⊥ V hV hY.1.le) hNbar hsylMbar).trans hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
