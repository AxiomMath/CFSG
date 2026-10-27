module

public import CFSG.Timmesfeld.Bridge.Asc72Triangle

import CFSG.OddTranspositions.PartThree.EightSix.OFourMinus
import CFSG.OddTranspositions.PartThree.EightSix.SecondKindSolvable
import CFSG.OddTranspositions.PartThree.EightSix.TriangleThree
public import CFSG.OddTranspositions.PartThree.EightFive.Holds
import CFSG.OddTranspositions.TheoremTwo.Assembly
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
public import Certificates.Certificate1383006
public import Certificates.Certificate1383007
public import Certificates.Certificate1383008
public import Certificates.Certificate1383009
public import Certificates.Certificate1430001
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCore
public import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddLocal CFSG.Timmesfeld.Connectivity


theorem isSolvable_of_connected_of_secondKind {X : Type} [Group X] [Finite X] {D : Set X}
    (hS : Setup X D) (hrad : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥)
    (hconn : ¬ Disconnected D) {u w v : X} (htri : IsTriangle D u w v)
    (h4 : orderOf (u * v * w) = 4) (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤) :
    Group.IsSolvable X := by
  by_cases hO : CFSG.OddTranspositions.QZ.O4PairData X D
  · obtain ⟨huw, hvw⟩ := orderOf_mul_eq_three_of_o4PairData hO htri h4
    exact isSolvable_of_orderOf_mul_eq_three
      (hS.oddT.mul_self_eq_one htri.1) (hS.oddT.mul_self_eq_one htri.2.2.1)
      (hS.oddT.mul_self_eq_one htri.2.1) htri.2.2.2.2.1 huw hvw hgen
  · by_contra hns
    have hns' : ¬ Group.IsSolvable (Subgroup.closure ({u, w, v} : Set X)) := by
      intro hsol
      apply hns
      rw [hgen] at hsol
      exact @Group.isSolvable_of_surjective ↥(⊤ : Subgroup X) X _ _
        (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom
        (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).surjective hsol
    obtain ⟨x, hxD, hxcl, htri', hthird⟩ :=
      exists_thirdKind_of_not_isSolvable hS.oddT hS.normal htri h4 hns'
    obtain ⟨hC⟩ := nonempty_hypothesisC hS hconn hrad
    obtain ⟨d, hdD, hdu, hdv, hdx⟩ :=
      theorem8_5_holds X D hC hrad hO u x v htri' hthird
    have hdw : Commute d w :=
      commute_of_commute_of_mem_closure hS.oddT htri.1 htri.2.2.1 htri.2.2.2.2.2.1
        hxD hxcl htri'.2.2.2.2.2.1 hdD hdu hdx
    have hdcent : d ∈ Subgroup.center X :=
      mem_center_of_commute_gen hgen (fun s hs => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl
        · exact hdu
        · exact hdw
        · exact hdv)
    have hcenterBot : Subgroup.center X = ⊥ :=
      hrad (Subgroup.center X) inferInstance
        (Group.isSolvable_of_comm fun a b =>
          Subtype.ext (Subgroup.mem_center_iff.mp b.2 a))
    have hd1 : d = 1 := by
      rw [hcenterBot, Subgroup.mem_bot] at hdcent
      exact hdcent
    exact hS.oddT.ne_one hdD hd1

end CFSG.OddTranspositions.PartThree.EightSix
