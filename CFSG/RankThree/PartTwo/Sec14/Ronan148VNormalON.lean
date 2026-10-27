module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148VNONGen
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJInner
import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormal

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Ronan148M Main148 Ronan148J
open CFSG.RankThree.Native.ONTriple

variable {G : Type} [Group G] [Finite G]

section Certificates



theorem img148_deltaZero_eq_of_innerON (h142 : Concl142S14) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h143 : Ronan148Q.Item143QS14) {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A) (ih : Ind148 A (lB A) Y)
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {J Yd : Subgroup G} (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hYdJ : Yd ≤ J) (hYdt : YdType148 d Yd)
    (hdc : d ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) (hdYd : d ∈ Yd) :
    letI := ker148_normal hY.2
    Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON →
    img148 A Y (deltaZero A (lB A) Y) = img148 A Y J := by
  intro hJON
  let := ker148_normal hY.2
  by_contra hXJ
  exact false_of_le_img148_of_innerON h134 h48 h143 hS hY ih hB hc hJ hAJ hYdJ hYdt hdc hdYd
    hJON hXJ (img148_le_deltaZero_of_innerON h142 hS hY hB hc hJ hAJ (hYdJ hdYd) hdc hJON)

theorem step148NormalHJONE_holds (h142 : Concl142S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h143 : Ronan148Q.Item143QS14) : Ronan148A.Step148NormalHJONE := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJON hdYd hdA hJn hdn
  let := ker148_normal hY.2
  have hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J :=
    img148_deltaZero_eq_of_innerON h142 h134 h48 h143 hS hY ih hB hc hJ hAJ hYdJ hYdt hdc hdYd
      hJON
  refine Ronan148A.map_normal_of_img148_eq (deltaZero_le Y) hXJ fun y hy => ?_
  set x := QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A))
  have hx := hJn x
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hx]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hx] at hh
    obtain ⟨h', hh', e⟩ := hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    have hh'h : h' = h := mul_left_cancel (mul_right_cancel e)
    rwa [← hh'h]

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
