module

public import CFSG.OddTranspositions.PartThree.EightFive.Holds
import CFSG.OddTranspositions.PartThree.EightSix.AlmostSimpleSub
import CFSG.OddTranspositions.TheoremTwo.ImageConnected
import CFSG.OddTranspositions.TheoremTwo.Assembly
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCore
public import CFSG.Permutation.BurnsideSchur
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.Fischer.NoF25.Local
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.OddTranspositions.AlmostSimple
import CFSG.OddTranspositions.Disconnected
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.WreathQuotient
import CFSG.Sporadic.Th.Max3.Data
import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.OddTranspositions
open CFSG.OddTranspositions.QZ

theorem exists_triangle_conjSet {X : Type} [Group X] {D : Set X} {M : Subgroup X}
    {u a v : X} (hta : IsTriangle D u a v) (hk : IsThirdKind u a v)
    (ham : ∃ m ∈ M, a = m * u * m⁻¹) (hvm : ∃ m ∈ M, v = m * u * m⁻¹) :
    ∃ u' a' v' : ↥(M ⊔ Subgroup.zpowers u),
      IsTriangle (conjSet M u) u' a' v' ∧ IsThirdKind u' a' v' ∧
        (u' : X) = u ∧ (a' : X) = a ∧ (v' : X) = v := by
  obtain ⟨ma, hma, ha_eq⟩ := ham
  obtain ⟨mv, hmv, hv_eq⟩ := hvm
  let K : Subgroup X := M ⊔ Subgroup.zpowers u
  have huK : u ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have haK : a ∈ K := by
    rw [ha_eq]
    exact K.mul_mem (K.mul_mem (Subgroup.mem_sup_left hma) huK)
      (K.inv_mem (Subgroup.mem_sup_left hma))
  have hvK : v ∈ K := by
    rw [hv_eq]
    exact K.mul_mem (K.mul_mem (Subgroup.mem_sup_left hmv) huK)
      (K.inv_mem (Subgroup.mem_sup_left hmv))
  let u' : K := ⟨u, huK⟩
  let a' : K := ⟨a, haK⟩
  let v' : K := ⟨v, hvK⟩
  have htri' : IsTriangle (conjSet M u) u' a' v' := by
    obtain ⟨-, -, -, huv, huvc, hua, hva⟩ := hta
    refine ⟨⟨1, one_mem M, by simp [u']⟩, ⟨mv, hmv, by simpa [v'] using hv_eq⟩,
      ⟨ma, hma, by simpa [a'] using ha_eq⟩, ?_, ?_, ?_, ?_⟩
    · intro h
      exact huv (by simpa [u', v'] using congrArg (fun k : K => (k : X)) h)
    · exact commute_coe_iff_of_subgroup.mp (by simpa [u', v'] using huvc)
    · intro h
      exact hua (by simpa [u', a'] using commute_coe_iff_of_subgroup.mpr h)
    · intro h
      exact hva (by simpa [v', a'] using commute_coe_iff_of_subgroup.mpr h)
  have hk' : IsThirdKind u' a' v' := by
    obtain ⟨n, hn, hn1, hord⟩ := hk
    exact ⟨n, hn, hn1, by
      rw [← Subgroup.orderOf_coe (u' * v' * a')]
      simpa [u', a', v'] using hord⟩
  exact ⟨u', a', v', htri', hk', rfl, rfl, rfl⟩

theorem mem_D_and_commute_of_mem_conjSet {X : Type} [Group X] {D : Set X}
    (hD : IsOddTransp D) (hN : IsNormalSet D) {M : Subgroup X} {u w v a : X}
    {d u' a' v' : ↥(M ⊔ Subgroup.zpowers u)} (hd : d ∈ conjSet M u)
    (htri : IsTriangle D u w v) (hta : IsTriangle D u a v)
    (haX : a ∈ Subgroup.closure {u, w})
    (hu' : (u' : X) = u) (ha' : (a' : X) = a) (hv' : (v' : X) = v)
    (hdu : Commute d u') (hda : Commute d a') (hdv : Commute d v') :
    (d : X) ∈ D ∧ Commute (d : X) u ∧ Commute (d : X) v ∧
      Commute (d : X) a ∧ Commute (d : X) w := by
  have hdD : (d : X) ∈ D := by
    obtain ⟨m, hm, hdm⟩ := hd
    rw [hdm]
    exact hN m u htri.1
  have hduX : Commute (d : X) u := by
    simpa [hu'] using hdu.map (Subgroup.subtype (M ⊔ Subgroup.zpowers u))
  have hdvX : Commute (d : X) v := by
    simpa [hv'] using hdv.map (Subgroup.subtype (M ⊔ Subgroup.zpowers u))
  have hdaX : Commute (d : X) a := by
    simpa [ha'] using hda.map (Subgroup.subtype (M ⊔ Subgroup.zpowers u))
  have hdw : Commute (d : X) w :=
    CFSG.Timmesfeld.Bridge.OddLocal.commute_of_commute_of_mem_closure hD htri.1
      htri.2.2.1 htri.2.2.2.2.2.1 hta.2.2.1 haX hta.2.2.2.2.2.1 hdD hduX hdaX
  exact ⟨hdD, hduX, hdvX, hdaX, hdw⟩


theorem false_of_thirdKind_conj {X : Type} [Group X] [Finite X] {D : Set X}
    (hD : IsOddTransp D) (hN : IsNormalSet D) {M : Subgroup X} [M.Normal]
    (hMs : IsSimpleGroup M) (hC : Subgroup.centralizer (M : Set X) = ⊥) {u w v a : X}
    (huM : u ∉ M) (hcls : IsOddTranspClass (conjSet M u)) (htri : IsTriangle D u w v)
    (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤) (huw : u * w ∉ M)
    (haX : a ∈ Subgroup.closure {u, w}) (hta : IsTriangle D u a v) (hk : IsThirdKind u a v)
    (ham : ∃ m ∈ M, a = m * u * m⁻¹) (hvm : ∃ m ∈ M, v = m * u * m⁻¹) : False := by
  classical
  let K : Subgroup X := M ⊔ Subgroup.zpowers u
  let Θ : Set K := conjSet M u
  have hS : Setup K Θ := ⟨by simpa [Θ] using hcls.1, by simpa [Θ] using hcls.2.1,
    by simpa [Θ] using hcls.2.2⟩
  have hM1 : M ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot M).mp hMs.toNontrivial
  have hrad : ∀ N : Subgroup K, N.Normal → Group.IsSolvable N → N = ⊥ :=
    solvable_normal_eq_bot_of_le le_sup_left hMs hC hM1
  have hconn : ¬ Disconnected Θ := by
    simpa [K, Θ] using not_disconnected_conjSet hMs hC huM hcls
  have hodd : Odd (orderOf (u * w)) :=
    hD.odd_of_not_commute htri.1 htri.2.2.1 htri.2.2.2.2.2.1
  have hO4 : ¬ O4PairData ↥K Θ := by
    simpa [K, Θ] using not_o4PairData_conjSet hMs hC huw hodd
  obtain ⟨hHC⟩ := nonempty_hypothesisC hS hconn hrad
  obtain ⟨u', a', v', htri', hk', hu'X, ha'X, hv'X⟩ :=
    exists_triangle_conjSet hta hk ham hvm
  obtain ⟨d, hdΘ, hdu, hdv, hda⟩ :=
    CFSG.OddTranspositions.PartThree.theorem8_5_holds K Θ hHC hrad hO4 u' a' v'
      htri' hk'
  obtain ⟨hdD, hduX, hdvX, hdaX, hdw⟩ :=
    mem_D_and_commute_of_mem_conjSet hD hN hdΘ htri hta haX hu'X ha'X hv'X hdu hda hdv
  have hle : (M : Set X) ⊆ (Subgroup.closure ({u, w, v} : Set X) : Set X) := by
    rw [hgen]
    exact fun _ _ => Subgroup.mem_top _
  have hdcent : (d : X) ∈ Subgroup.centralizer (M : Set X) := by
    have htop : (d : X) ∈ Subgroup.centralizer
        (Subgroup.closure ({u, w, v} : Set X) : Set X) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · exact hduX.symm
      · exact hdw.symm
      · exact hdvX.symm
    exact Subgroup.centralizer_le hle htop
  have hd1 : (d : X) = 1 := by
    have hmem := hdcent
    rw [hC] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hord : orderOf (d : X) = 2 := hD.1 (d : X) hdD
  rw [hd1, orderOf_one] at hord
  omega

end CFSG.OddTranspositions.PartThree.EightSix

end
