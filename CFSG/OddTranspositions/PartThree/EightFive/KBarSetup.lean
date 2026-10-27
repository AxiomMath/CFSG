module

public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCoreBasic
public import CFSG.OddTranspositions.O4PairNoSq
public import CFSG.OddTranspositions.SevenThreeQuotient
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.OddTranspositions.SixEight
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72XEnd
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def centSetBar (D : Set G) (z : G) :
    Set (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)) :=
  (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z))) '' localSet D z

@[expose] def mkCentSet (D : Set G) (z x : G) (hx : x ∈ centSet D z) :
    localGroup D z ⧸ CFSG.solvableRadical (localGroup D z) :=
  QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z))
    (⟨x, mem_localGroup_of_mem hx⟩ : localGroup D z)

omit [Finite G] in
theorem mem_centSetBar_mkCentSet {z x : G} (hx : x ∈ centSet D z) :
    mkCentSet D z x hx ∈ centSetBar D z :=
  ⟨⟨x, mem_localGroup_of_mem hx⟩, hx, rfl⟩

theorem setup_centSetBar_of_transitive (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n)
    (htrans : ∀ x ∈ centSet D ((u * v * w) ^ n),
      ∃ k ∈ localGroup D ((u * v * w) ^ n), k * u * k⁻¹ = x) :
    Setup (localGroup D ((u * v * w) ^ n) ⧸
        CFSG.solvableRadical (localGroup D ((u * v * w) ^ n)))
      (centSetBar D ((u * v * w) ^ n)) := by
  classical
  let z : G := (u * v * w) ^ n
  let K : Subgroup G := localGroup D z
  let R : Subgroup K := CFSG.solvableRadical K
  obtain ⟨-, -, hzu, -, -, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  have huC : u ∈ centSet D z := ⟨htri.1, hzu.symm⟩
  have hclass : ∃ d₀ : K, localSet D z = {x | IsConj d₀ x} := by
    refine ⟨⟨u, mem_localGroup_of_mem huC⟩, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, hkx⟩ := htrans (x : G) hx
      exact isConj_iff.mpr ⟨⟨k, hk⟩, Subtype.ext hkx⟩
    · intro hx
      rw [Set.mem_setOf_eq] at hx
      rw [isConj_iff] at hx
      obtain ⟨c, hc⟩ := hx
      have hcG : (c : G) * u * (c : G)⁻¹ = (x : G) := congrArg Subtype.val hc
      have hx' : (x : G) ∈ centSet D z := by
        rw [← hcG]
        exact ⟨hS.normal (c : G) u htri.1,
          ((commute_of_mem_localGroup c.2).mul_left hzu.symm).mul_left
            (commute_of_mem_localGroup c.2).inv_left⟩
      exact hx'
  rcases hclass with ⟨d₀, hclass'⟩
  refine
    { isClass := image_isClass_quotient hclass' R
      oddT := image_isOddTransp_quotient R
        ((hS.oddT.preimage K).mono (fun x hx => hx.1))
        (fun x hx => mk_centSet_ne_one hS htri hn hn1 hord rfl htrans hx x.2)
      gen := image_closure_eq_top_quotient R Subgroup.closure_closure_coe_preimage }

theorem mkCentSet_u_v_spec (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n)
    (htrans : ∀ x ∈ centSet D ((u * v * w) ^ n),
      ∃ k ∈ localGroup D ((u * v * w) ^ n), k * u * k⁻¹ = x)
    (huC : u ∈ centSet D ((u * v * w) ^ n))
    (hvC : v ∈ centSet D ((u * v * w) ^ n)) :
    mkCentSet D ((u * v * w) ^ n) u huC ≠ mkCentSet D ((u * v * w) ^ n) v hvC ∧
    Commute (mkCentSet D ((u * v * w) ^ n) u huC)
      (mkCentSet D ((u * v * w) ^ n) v hvC) ∧
    mkCentSet D ((u * v * w) ^ n) u huC *
      mkCentSet D ((u * v * w) ^ n) v hvC ∈ centSetBar D ((u * v * w) ^ n) := by
  classical
  let z : G := (u * v * w) ^ n
  let K : Subgroup G := localGroup D z
  let R : Subgroup K := CFSG.solvableRadical K
  let mk := QuotientGroup.mk' R
  obtain ⟨hzz, -, hzu, hzv, -, hbD⟩ := IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  have hbz : Commute (u * v * z) z :=
    ((hzu.symm.mul_left hzv.symm).symm.mul_right (Commute.refl z)).symm
  have hbC : u * v * z ∈ centSet D z := ⟨hbD, hbz⟩
  have huK : u ∈ K := mem_localGroup_of_mem huC
  have hvK : v ∈ K := mem_localGroup_of_mem hvC
  have hbK : u * v * z ∈ K := mem_localGroup_of_mem hbC
  have hzK : z ∈ K := thirdKind_z_mem_localGroup hS htri hn hord
  have hzR : (⟨z, hzK⟩ : K) ∈ R := by
    have hzCenter : (⟨z, hzK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (commute_of_mem_localGroup k.2)
    exact OddTransp.le_solvableRadical (N := Subgroup.center K) inferInstance inferInstance hzCenter
  have hmemBar : ∀ {x : G} (hx : x ∈ centSet D z),
      mk ⟨x, mem_localGroup_of_mem hx⟩ ∈ centSetBar D z :=
    fun {x} hx => ⟨⟨x, mem_localGroup_of_mem hx⟩, hx, rfl⟩
  have hmul : mk ⟨u, huK⟩ * mk ⟨v, hvK⟩ = mk ⟨u * v * z, hbK⟩ := by
    have huv_eq : (⟨u, huK⟩ * ⟨v, hvK⟩ : K) = ⟨u * v * z, hbK⟩ * ⟨z, hzK⟩ := by
      apply Subtype.ext
      show u * v = u * v * z * z
      rw [mul_assoc (u * v), hzz, mul_one]
    have hzR1 : mk ⟨z, hzK⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hzR
    rw [← map_mul, huv_eq, map_mul, hzR1, mul_one]
  have huu : (⟨u, huK⟩ : K) * ⟨u, huK⟩ = 1 :=
    Subtype.ext (hS.oddT.mul_self_eq_one htri.1)
  have hne : mk ⟨u, huK⟩ ≠ mk ⟨v, hvK⟩ := by
    intro hEq
    have hb1 : mk ⟨u * v * z, hbK⟩ = 1 := by
      rw [← hmul, ← hEq, ← map_mul, huu, map_one]
    exact mk_centSet_ne_one hS htri hn hn1 hord rfl htrans hbC hbK hb1
  have hcomm : Commute (⟨u, huK⟩ : K) ⟨v, hvK⟩ :=
    (commute_iff_eq _ _).mpr (Subtype.ext htri.2.2.2.2.1.eq)
  exact ⟨hne, hcomm.map mk, hmul ▸ hmemBar hbC⟩

theorem exists_meetsSq_centSetBar (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n)
    (htrans : ∀ x ∈ centSet D ((u * v * w) ^ n),
      ∃ k ∈ localGroup D ((u * v * w) ^ n), k * u * k⁻¹ = x) :
    ∃ x ∈ centSetBar D ((u * v * w) ^ n),
      ∃ y ∈ centSetBar D ((u * v * w) ^ n),
        x ≠ y ∧ Commute x y ∧ x * y ∈ centSetBar D ((u * v * w) ^ n) := by
  obtain ⟨huC, hvC, -, -⟩ := thirdKind_mem_centSet hS htri hn hord
  obtain ⟨hne, hcomm, hmul⟩ := mkCentSet_u_v_spec hS htri hn hn1 hord htrans huC hvC
  exact ⟨_, mem_centSetBar_mkCentSet huC, _, mem_centSetBar_mkCentSet hvC,
    hne, hcomm, hmul⟩

theorem not_commute_mk_v_w_of_transitive (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n)
    (htrans : ∀ x ∈ centSet D ((u * v * w) ^ n),
      ∃ k ∈ localGroup D ((u * v * w) ^ n), k * u * k⁻¹ = x)
    (hvC : v ∈ centSet D ((u * v * w) ^ n))
    (hwC : w ∈ centSet D ((u * v * w) ^ n))
    (hvK : v ∈ localGroup D ((u * v * w) ^ n))
    (hwK : w ∈ localGroup D ((u * v * w) ^ n)) :
    ¬ Commute
      (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D ((u * v * w) ^ n)))
        (⟨v, hvK⟩ : localGroup D ((u * v * w) ^ n)))
      (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D ((u * v * w) ^ n)))
        (⟨w, hwK⟩ : localGroup D ((u * v * w) ^ n))) := by
  have hvu : v * u = u * v := htri.2.2.2.2.1.eq.symm
  have htri' : IsTriangle D v w u :=
    ⟨htri.2.1, htri.1, htri.2.2.1, htri.2.2.2.1.symm, htri.2.2.2.2.1.symm,
      htri.2.2.2.2.2.2, htri.2.2.2.2.2.1⟩
  have hord' : orderOf (v * u * w) = 2 * n := by
    rw [hvu]
    exact hord
  have hzdef' : (v * u * w) ^ n = (u * v * w) ^ n := by rw [hvu]
  have htrans_v : ∀ x ∈ centSet D ((u * v * w) ^ n),
      ∃ k ∈ localGroup D ((u * v * w) ^ n), k * v * k⁻¹ = x :=
    transitive_pair_of_transitive htrans v hvC
  exact not_commute_mk_u_w hS htri' hn hn1 hord' hzdef' htrans_v hvC hwC hvK hwK

end CFSG.OddTranspositions.PartThree
