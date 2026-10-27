module

public import CFSG.OddTranspositions.PartFour.RootMeetsSq
public import CFSG.OddTranspositions.PartFour.SeventeenFourU
import CFSG.OddTranspositions.PartFour.Fourteen.TableMeetsSq

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem meetsSq_of_isUnitaryTransvection_imageClass (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {d f : ℕ} (hd : 4 ≤ d) (hf : 2 ≤ f)
    (hut : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) d f s) :
    MeetsSq D := by
  have hZ := center_eq_bot_quotient_H hC
  have hcls := imageClass_eq_setOf_isConj hC hs
  have hsq : MeetsSq (imageClass hC) :=
    meetsSq_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs hf hut
  have hHns := not_isSolvable_Halpha_of_meetsSq hC hsq
  have hn3 := not_threeTransp_of_meetsSq hC hsq
  have hfour := exists_four_of_isUnitaryTransvection hZ hd hut
  rw [← hcls] at hfour
  refine meetsSq_of_root h89 h113 hC hrad hW hMZ hsq hfour (fun x hx => ?_) (fun x hx => ?_)
    fun β hβ => ncard_blockImage_blockLine_diff_eq_one_of_eq_insert hC hβ
      (blockLine_eq_insert_orbit_of_isUnitaryTransvection h89 h113 hC hrad hW hn3 hMZ hHns hs hd
        hut hβ).1
  · have h := exists_subgroup_eq_insert_Vmem_of_isUnitaryTransvection hZ (by omega) hut (x := x)
      (by rw [← hcls]; exact hx)
    rwa [← hcls] at h
  · have h := ncard_Vmem_of_isUnitaryTransvection hZ (by omega) hut (x := x)
      (by rw [← hcls]; exact hx)
    rw [← hcls] at h
    rw [h]
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega

end CFSG.OddTranspositions.PartFour
