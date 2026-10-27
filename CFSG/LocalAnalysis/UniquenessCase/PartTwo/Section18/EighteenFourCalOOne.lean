module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwoProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourBarSub
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarSevenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem bBar_conjClosure_le_two_of_isAlt {D : Data G} {V₀ V L : Subgroup G}
    (hp : Hyp125 D V₀ V) (hL : L ∈ calC D.M) (h77 : Inputs1719.W4Lem7_7)
    (hL1 : barSub V₀ V hp.isElemAbelian L ≠ ⊥) (hAlt : IsAlt (Bar2 L) 5) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hp.isElemAbelian ≤ 2 := by
  classical
  refine bBar_conjClosure_le_of_candidate_bound_of_hyp125 hp hL h77 hL1 fun g n hn => ?_
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hp.pairFacts.le_normalizer hp.pairFacts.le_normalizer₀
  have hK : L.map (MulAut.conj (g : G)).toMonoidHom ∈ calC D.M :=
    uc22p2214_calC_of_mem_conjSetOf hL ⟨(g : G), g.2, rfl⟩
  have hKne : barSub V₀ V hp.isElemAbelian
      (L.map (MulAut.conj (g : G)).toMonoidHom) ≠ ⊥ := by
    rw [TwelveTwentyThree.barSub_map_conj hp.isElemAbelian (hL.1.le.trans hMS) (hMS g.2)]
    intro hbot
    rw [Subgroup.map_eq_bot_iff] at hbot
    have hker : (MulAut.conj
        ((actTil V₀ V hp.isElemAbelian) ⟨(g : G), hMS g.2⟩)).toMonoidHom.ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]
      exact (MulAut.conj _).injective
    rw [hker] at hbot
    exact hL1 (le_bot_iff.1 hbot)
  have hKalt : IsAlt (Bar2 (L.map (MulAut.conj (g : G)).toMonoidHom)) 5 := by
    obtain ⟨e⟩ := S17.bar2_conj_equiv L (g : G)
    exact ⟨e.symm.trans hAlt.some⟩
  exact aCandidate_le_two_of_isAlt_five
    (isAlt_barSub_of_isAlt_bar2 hp hK hKne hKalt) n hn

namespace A5Pair18

variable {D : Data G} {V₀ V L K : Subgroup G}

theorem calO_one_eq_empty
    (c : A5Pair18 D V₀ V L K) (hV₀ : V₀ ≠ ⊥) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h77 : Inputs1719.W4Lem7_7) : calO 1 D.M V₀ V = ∅ := by
  classical
  have h3 : MBarGT D.M V₀ V 3 :=
    mBarGT_three_of_hyp18 D c.data.hyp h1669
  have hm4 : 4 ≤ mBar D.M V₀ V c.data.hyp.hyp125.isElemAbelian := by
    have h := (c.data.hyp.hyp125.mBarGT_iff_lt_mBar 3).1 h3
    omega
  have key : ∀ J : Subgroup G, J ∈ calC D.M → IsAlt (Bar2 J) 5 →
      barSub V₀ V c.data.hyp.hyp125.isElemAbelian J ≠ ⊥ → calO 1 D.M V₀ V = ∅ := by
    intro J hJ hJalt hJ1
    have hb2 : bBar (UC22.conjClosure D.M J) D.M V₀ V
        c.data.hyp.hyp125.isElemAbelian ≤ 2 :=
      bBar_conjClosure_le_two_of_isAlt c.data.hyp.hyp125 hJ h77 hJ1 hJalt
    have hb : bBar (UC22.conjClosure D.M J) D.M V₀ V c.data.hyp.hyp125.isElemAbelian <
        mBar D.M V₀ V c.data.hyp.hyp125.isElemAbelian - 1 := by omega
    have hXM : UC22.conjClosure D.M J ≤ D.M := TwelveTwentyThree.conjClosure_le hJ.1.le
    have hXn : D.M ≤ normalizer (UC22.conjClosure D.M J : Set G) :=
      TwelveTwentyThree.le_normalizer_conjClosure D.M J
    have hX1 : barSub V₀ V c.data.hyp.hyp125.isElemAbelian
        (UC22.conjClosure D.M J) ≠ ⊥ :=
      TwelveTwentyThree.barSub_conjClosure_ne_bot c.data.hyp.hyp125.isElemAbelian hJ1
    have hab : XCond1218 D.M V₀ V c.data.hyp.hyp125.isElemAbelian 1
        (UC22.conjClosure D.M J) :=
      TwelveTwentyThree.xCond1218_conjClosure c.data.hyp.hyp125 hV₀ hJ.1 hJ.2.2 1
    have hemp := twelve_eighteen_empty D hx h61 h127 h1114 h162 hTor h1482
      c.data.hyp.hyp125 hV₀ hXM hXn hX1 hb hab
    rw [Set.eq_empty_iff_forall_notMem]
    rintro X ⟨g, rfl, hO⟩
    exact hemp g hO
  rcases c.barSub_ne_bot_or h61 h127 with hL1 | hK1
  · exact key L c.mem_calC_L c.data.alt hL1
  · exact key K c.mem_calC c.alt_K hK1

theorem r18_2At
    (c : A5Pair18 D V₀ V L K) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (h126 : R126 D)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h77 : Inputs1719.W4Lem7_7) : R18_2At D V₀ V 5 L c.data.hyp :=
  eighteen_two_of_calO_one D hx h61 h127 h1114 h162 h126 c.data.hyp
    (fun hV₀ => c.calO_one_eq_empty hV₀ hx h61 h127 h1114 h162 hTor h1482 h1669 h77)

end A5Pair18

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
