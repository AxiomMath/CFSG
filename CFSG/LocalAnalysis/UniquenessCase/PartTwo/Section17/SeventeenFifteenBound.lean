module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenThreeConjInFSq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarConjShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubInFSq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsNoO2Sixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def B17_15BoundK2 (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥ → IsL2Over17 (Bar2 L) 7 →
    CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)) → D.k = 2 →
    fixV (barSub V₀ V hC.hyp125.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ →
      bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ 1

theorem b17_15BoundK2_holds (h410 : W4Lem4_10) (h43c : W3Lem45_2Chief)
    (hW4 : Inputs1719.W4Lem4_16b) (D : Data G) (h82 : F08.R82 D) {V₀ V L : Subgroup G}
    {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q) : B17_15BoundK2 D V₀ V L r q hC := by
  intro hLb h7 hPGL hk hfix
  have hV := hC.hyp125
  have hLM : L ≤ D.M := hC.memL.1.le
  have htri : ∀ x ∈ D.M, ∀ y ∈ D.M,
      L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj y).toMonoidHom = L ∨
      L.map (MulAut.conj y).toMonoidHom = L.map (MulAut.conj x).toMonoidHom := by
    intro x hx y hy
    by_contra hcon
    push Not at hcon
    have h1 : D.k = 1 :=
      k_eq_one_of_three_conj D h82 hC.memL h7 hx hy hcon.1 hcon.2.1 hcon.2.2
    omega
  have htr : ∀ g ∈ D.M, ∃ t ∈ D.T,
      L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom :=
    exists_T_conj_eq_of_two_conj D htri
  have hIn : InFSq 1 (L ⊔ D.T) :=
    gap17_15_threeConjInFSq_holds h410 h43c D hC h7 hPGL
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  have hLS : L ≤ stabTil V₀ V := hLM.trans hMS
  have hTS : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMS
  have hZ : Subgroup.center (UC22.Bar2 L) = ⊥ := by
    have : IsSimpleGroup (UC22.Bar2 L) :=
      LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide)
        (isL2Odd_seven_of_isL2Over17_seven h7)
    exact uc22p21k_center_eq_bot hC.memL.2.2
  have hbar0 : InFSq 1 (barSub V₀ V hV.isElemAbelian (L ⊔ D.T)) :=
    inFSq_barSub_of_le_sup_T hV hC.memL hZ hLb (le_refl _) hIn
  rw [s16c7_barSub_sup V₀ V hV.isElemAbelian hLS hTS] at hbar0
  have hInY : InFSq 1 (barSub V₀ V hV.isElemAbelian L ⊔
      barSub V₀ V hV.isElemAbelian D.T) := by
    simpa using hbar0
  have hcomp : IsComponentOf (barSub V₀ V hV.isElemAbelian L)
      (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T) := by
    refine CFSG.Quasithin.B15P4.isComponentOf_of_le
      (X := Mbar D.M V₀ V hV.isElemAbelian) ?_ le_sup_left ?_
    · simpa [compBar] using barSub_mem_compBar_of_ne_bot hV hC.memL hLb
    · exact sup_le (barSub_mono V₀ V hV.isElemAbelian hLM)
        (barSub_mono V₀ V hV.isElemAbelian D.sylowM.le)
  have hsyl : IsSylowIn 2 (barSub V₀ V hV.isElemAbelian D.T)
      (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T) := by
    have h := isSylowIn_barSub_T_sup hV hLM
    rwa [s16c7_barSub_sup V₀ V hV.isElemAbelian hLS hTS] at h
  have hLX : barSub V₀ V hV.isElemAbelian L ≤
      barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) :=
    barSub_mono V₀ V hV.isElemAbelian (TwelveTwentyThree.le_conjClosure D.M L)
  have hXne : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥ := by
    intro hbot
    exact hLb (le_bot_iff.1 (hLX.trans (le_of_eq hbot)))
  have hXle : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) ≤
      barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T :=
    barSub_conjClosure_le_sup_T_of_transitive hV hLM htr
  have hsupX : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) ⊔
      barSub V₀ V hV.isElemAbelian D.T =
      barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T :=
    le_antisymm (sup_le hXle le_sup_right) (sup_le_sup hLX le_rfl)
  have hfixT : fixV (barSub V₀ V hV.isElemAbelian D.T) ≠
      fixV (barSub V₀ V hV.isElemAbelian L ⊔
        barSub V₀ V hV.isElemAbelian D.T) := by
    have hne := fixV_ne_fixV_sup (W := Vtil V₀ V hV.isElemAbelian)
      (s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian) hXne hfix hsyl.isPGroup
    rwa [hsupX] at hne
  have hsum : fIndexSum ({(barSub V₀ V hV.isElemAbelian L ⊔
      barSub V₀ V hV.isElemAbelian D.T)} :
        Set (Subgroup (MulAut (Vtil V₀ V hV.isElemAbelian)))) ≤ (1 : ℕ∞) := by
    rw [fIndexSum, finsum_mem_singleton]
    exact fIndex_le_iff.mpr hInY
  have hbound : bParam (barSub V₀ V hV.isElemAbelian L)
      (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T) ≤ 1 :=
    hW4 (Vtil V₀ V hV.isElemAbelian) (s15_Infra_vtil_sq_eq_one V₀ V hV.isElemAbelian)
      (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T)
      (barSub V₀ V hV.isElemAbelian L) (barSub V₀ V hV.isElemAbelian D.T)
      {(barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T)} 1
      le_sup_left le_sup_right rfl hcomp hsyl (Set.finite_singleton _)
      (by rintro H rfl; exact ⟨le_rfl, le_sup_right⟩) (by simp) hsum hfixT
  calc bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian
      ≤ bParam (barSub V₀ V hV.isElemAbelian L)
          (barSub V₀ V hV.isElemAbelian L ⊔
            barSub V₀ V hV.isElemAbelian D.T) :=
        bBar_conjClosure_le_bParam_sup_of_transitive hV hLM htr
    _ ≤ 1 := hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
