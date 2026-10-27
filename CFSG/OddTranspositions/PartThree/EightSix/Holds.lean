module

public import CFSG.OddTranspositions.PartThree.EightSix.Generated
public import CFSG.OddTranspositions.PartThree.EightFive.Holds
public import Certificates.Certificate1383006
public import Certificates.Certificate1383007
public import Certificates.Certificate1383008
public import Certificates.Certificate1383009
public import Certificates.Certificate1430001

import CFSG.OddTranspositions.PartThree.EightSix.AlmostSimple
import CFSG.OddTranspositions.PartThree.EightSix.AlmostSimpleQuot
import CFSG.OddTranspositions.PartThree.EightSix.Bender
import CFSG.OddTranspositions.PartThree.EightSix.Connected
import CFSG.OddTranspositions.PartThree.EightSix.Reduce
import CFSG.OddTranspositions.PartThree.EightSix.Wreath
import CFSG.Timmesfeld.Bridge.Asc72ZMain
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCore
public import CFSG.Permutation.BurnsideSchur
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.BenderSuzuki CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity


theorem isSolvable_of_disconnected_of_secondKind {X : Type} [Group X] [Finite X] {D : Set X}
    (hS : Setup X D) (hrad : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥)
    (hdisc : Disconnected D) {u w v : X} (htri : IsTriangle D u w v)
    (h4 : orderOf (u * v * w) = 4) (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤) :
    Group.IsSolvable X := by
  classical
  obtain ⟨H, hHtop, ⟨x, hx, hxH⟩, hclosed⟩ := exists_subgroup_of_disconnected hS hdisc
  rcases theoremOne X D hS.isClass hS.oddT.1 hS.oddT.2 hS.gen hrad
      ⟨H, hHtop, ⟨x, hx, hxH⟩, hclosed⟩ with hB | hW | hAS
  · exact absurd h4 (orderOf_mul_ne_four_of_isBenderGroup hB hS.oddT.1 htri)
  · obtain ⟨f, n, hf, hn, ⟨e⟩⟩ := hW
    exact isSolvable_of_l2Wreath_of_triangle hS hrad hf hn e htri hgen
  · obtain ⟨M, hMn, -, -, hMs, hC, hidx, hWidth, hcls⟩ := hAS
    let : M.Normal := hMn
    obtain ⟨huM, huwM, ⟨mv, hmv, hv⟩, a, -, haX, hta, hk, ma, hma, haeq⟩ :=
      exists_thirdKind_conj_of_almostSimple hS hMs hC hidx hWidth htri h4 hgen
    exact (false_of_thirdKind_conj hS.oddT hS.normal hMs hC huM (hcls u htri.1) htri hgen
      huwM haX hta hk ⟨ma, hma, haeq⟩ ⟨mv, hmv, hv⟩).elim

theorem isSolvable_of_generated_aux (n : ℕ) :
    ∀ (X : Type) [Group X] [Finite X] (D : Set X), Nat.card X = n → Setup X D →
      ∀ u w v : X, IsTriangle D u w v → orderOf (u * v * w) = 4 →
        Subgroup.closure ({u, w, v} : Set X) = ⊤ → Group.IsSolvable X := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X _ _ D hcard hS u w v htri h4 hgen
    classical
    have hind : ∀ (Y : Type) [Group Y] [Finite Y] (E : Set Y), Nat.card Y < Nat.card X →
        Setup Y E → ∀ a b c : Y, IsTriangle E a b c → orderOf (a * c * b) = 4 →
          Subgroup.closure ({a, b, c} : Set Y) = ⊤ → Group.IsSolvable Y := by
      intro Y _ _ E hY hSY a b c htriY h4Y hgenY
      exact ih (Nat.card Y) (hcard ▸ hY) Y E rfl hSY a b c htriY h4Y hgenY
    by_cases hN : ∃ N : Subgroup X, N.Normal ∧ N ≠ ⊥ ∧ Group.IsSolvable N
    · obtain ⟨N, hNn, hN1, hNsolv⟩ := hN
      let : N.Normal := hNn
      exact isSolvable_of_quotient_secondKind hS htri h4 hgen hNsolv hN1 hind
    · have hrad : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥ := by
        intro N hNn hNsolv
        by_contra hN1
        exact hN ⟨N, hNn, hN1, hNsolv⟩
      by_cases hdisc : Disconnected D
      · exact isSolvable_of_disconnected_of_secondKind hS hrad hdisc htri h4 hgen
      · exact isSolvable_of_connected_of_secondKind hS hrad hdisc htri h4 hgen

theorem isSolvable_of_generated {X : Type} [Group X] [Finite X] {D : Set X}
    (hS : Setup X D) {u w v : X} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤) : Group.IsSolvable X :=
  isSolvable_of_generated_aux (Nat.card X) X D rfl hS u w v htri h4 hgen

theorem lemma8_6_holds : Lemma8_6 :=
  lemma8_6_of_generated fun _ _ _ _ hS _ _ _ htri hord hgen =>
    isSolvable_of_generated hS htri hord hgen

end CFSG.OddTranspositions.PartThree.EightSix
