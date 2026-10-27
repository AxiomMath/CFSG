module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarSevenSeven
public import CFSG.GroupTheory.QuasisimpleCentralInvolution
public import CFSG.Timmesfeld.Bridge.RootSetsConn5
public import CFSG.Goldschmidt.Steps.LemmaXCore
public import CFSG.Quasithin.Background.E4Solv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem bBar_pos_of_barSub_ne_bot {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q)
    (hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥) :
    0 < bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian := by
  classical
  have hV := hC.hyp125
  have hL := hC.memL
  have hp := hV.pairFacts
  have hLM : L ≤ D.M := hL.1.le
  have hLS : L ≤ stabTil V₀ V := hLM.trans (le_stabTil hp.le_normalizer hp.le_normalizer₀)
  have h2 : barSub V₀ V hV.isElemAbelian (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV.isElemAbelian hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 hV)
  have hLbq : CFSG.Open.IsQuasisimple ↥(barSub V₀ V hV.isElemAbelian L) :=
    TwelveTwentyThree.isQuasisimple_barSub hV.isElemAbelian hLS hL.2.2 h2 hL1
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(barSub V₀ V hV.isElemAbelian L)) 2
    (CFSG.Goldschmidt.LemmaX.two_dvd_card_of_isQuasisimple hLbq)
  have hO2 : CFSG.pCore 2 (Bar2 L) = ⊥ :=
    CFSG.Timmesfeld.Bridge.pCore_two_quotient_pCore_eq_bot
  have htcent : t ∉ Subgroup.center ↥(barSub V₀ V hV.isElemAbelian L) :=
    CFSG.GroupTheory.not_mem_center_of_orderOf_eq_two_of_quasisimple
      (barSubBar2HomOfHyp125 hV hL) (barSubBar2HomOfHyp125_surjective hV hL)
      hL.2.2 hO2 ht
  have htne : t ≠ 1 := by rintro rfl; simp at ht
  have ht2 : (t : MulAut (Vtil V₀ V hV.isElemAbelian)) ^ 2 = 1 := by
    have hord : orderOf (t : MulAut (Vtil V₀ V hV.isElemAbelian)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact ht
    rw [← hord, pow_orderOf_eq_one]
  let A : Subgroup (MulAut (Vtil V₀ V hV.isElemAbelian)) :=
    Subgroup.zpowers (t : MulAut (Vtil V₀ V hV.isElemAbelian))
  have hA_le : A ≤ Mbar D.M V₀ V hV.isElemAbelian := by
    intro a ha
    have htmem : (t : MulAut (Vtil V₀ V hV.isElemAbelian)) ∈
        barSub V₀ V hV.isElemAbelian L := t.2
    exact barSub_mono V₀ V hV.isElemAbelian hLM (Subgroup.zpowers_le.2 htmem ha)
  have hA_ne : A ≠ ⊥ := by
    intro hbot
    have h1 : (t : MulAut (Vtil V₀ V hV.isElemAbelian)) = 1 :=
      (Subgroup.zpowers_eq_bot).1 hbot
    exact htne (Subtype.ext h1)
  have hA_mem : A ∈ CFSG.Quasithin.E3.aSet 1 (Mbar D.M V₀ V hV.isElemAbelian) := by
    rw [CFSG.Quasithin.E3.aSet_one]
    exact ⟨hA_le, hA_ne, CFSG.Quasithin.E3.isElemAbelian2_zpowers ht2⟩
  have hX_ne : ⁅barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L), A⁆ ≠ ⊥ := by
    intro hcomm
    apply htcent
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hXle : barSub V₀ V hV.isElemAbelian L ≤
        barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) :=
      barSub_mono V₀ V hV.isElemAbelian (TwelveTwentyThree.le_conjClosure D.M L)
    have hlX : (l : MulAut (Vtil V₀ V hV.isElemAbelian)) ∈
        barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) := hXle l.2
    have hcent := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm hlX
    have h1 := (Subgroup.mem_centralizer_iff).1 hcent
      (t : MulAut (Vtil V₀ V hV.isElemAbelian)) (Subgroup.mem_zpowers _)
    exact h1.symm
  have hb : 1 ≤ bParam (barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L))
      (Mbar D.M V₀ V hV.isElemAbelian) :=
    le_bParam (k := 1) (by norm_num) hA_mem hX_ne
  simp only [bBar]
  omega


theorem seventeen_eleven_of_bounds {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    {hC : Ctx17_6 D V₀ V L r q} (h17_9 : R17_9At D V₀ V L r q hC)
    (hb2 : bBar (conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ 2)
    (hb1 : 9 < q → bBar (conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ 1) :
    R17_11At D V₀ V L r q hC := by
  intro hL1
  have hpos := bBar_pos_of_barSub_ne_bot hC hL1
  have hq3 : 3 < q := h17_9
  by_cases hq : 9 < q
  · left
    have := hb1 hq
    omega
  · by_cases hb1' : bBar (conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian = 1
    · exact Or.inl hb1'
    · right
      exact ⟨by omega, by omega⟩

theorem seventeen_eleven (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) (h17_9 : R17_9At D V₀ V L r q hC)
    (h77 : Inputs1719.W4Lem7_7) (h106 : Inputs1719.W4Lem10_6Q) :
    R17_11At D V₀ V L r q hC := by
  intro hL1
  exact seventeen_eleven_of_bounds h17_9
    (bBar_conjClosure_le_two hC h77 h106 hL1 h17_9)
    (fun hq => bBar_conjClosure_le_one hC h77 h106 hL1 hq) hL1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
