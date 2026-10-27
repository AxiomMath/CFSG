module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec311bComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec7Hyp.not_slNat {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) :
    ¬ SLNat hc t := by
  intro hsl
  obtain ⟨m, hm, hpm⟩ := hs.orth
  rcases hpm with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · have hm3 : 3 ≤ m := by
      by_contra hlt
      have h2 : m = 2 := by omega
      subst h2
      exact hs.notPlus4 ⟨K, fK, finK, hK, hnat⟩
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    exact not_slNat_of_orth hc hsl hK (ElemMatrixIso.plus hm3)
      (nondegenerate_polarBilin_quadPlus m K) hnat (by simp; omega)
  · haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    exact not_slNat_of_orth hc hsl hK (ElemMatrixIso.minus hm hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) hnat (by simp; omega)

theorem sec7CommN_of_311b (h311 : Stroth311bCommStatement) : Sec7CommNStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have hs5 := hs.toSec5
  obtain ⟨T, hT⟩ := exists_centLB hc t
  have hNT := h311 G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t hs5.mem hs5.notQ
    (sec7_Rt_ne_LB hc hs) hs.not_slNat T hT
  intro x hx
  obtain ⟨hxL, hxr⟩ := (hT x).mp (hNT hx)
  refine (hZ0 x).mpr ⟨le_Rt (M := M) (LB M Q B) hs5.mem hxL, fun r hr => ?_⟩
  rw [← commutatorElement_inv]
  exact Q.inv_mem (hxr r hr)

theorem sec7CommN_of_34 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h311a : Stroth311aStatement) : Sec7CommNStatement :=
  sec7CommN_of_311b (stroth311bComm_of_34 h34 h310 h311a)

end CFSG.RankThree.GF2n.Stroth80

end
