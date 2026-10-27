module

public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Bridge.OddTranspDefs
public import CFSG.OddTranspositions.PartThree.Statements

import CFSG.OddTranspositions.PartThree.EightEight.Fibres
import CFSG.OddTranspositions.PartThree.EightEight.SecondKind
import CFSG.Timmesfeld.Bridge.OddTranspSecondKind
import CFSG.OddTranspositions.PartThree.SixThreeGlobal
import CFSG.GroupTheory.Commutator.ZPowersInvolution
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {E : Set X}

omit [Finite X] in
theorem isTriangle_of_mk_ne (hS : Setup X E) {y y' c : X} (hy : y ∈ E) (hy' : y' ∈ E)
    (hc : c ∈ E) (hyy' : Commute y y') (hne : y ≠ y')
    (hfib : QuotientGroup.mk' (derivedSeries X 2) c ≠ QuotientGroup.mk' (derivedSeries X 2) y) :
    IsTriangle E y c y' := by
  have hyy'mk : QuotientGroup.mk' (derivedSeries X 2) y =
      QuotientGroup.mk' (derivedSeries X 2) y' := mk_eq_mk_of_commute hS hy hy' hyy'
  refine ⟨hy, hy', hc, hne, hyy', ?_, ?_⟩
  · intro hyc
    exact hfib (mk_eq_mk_of_commute hS hy hc hyc).symm
  · intro hy'c
    have h : QuotientGroup.mk' (derivedSeries X 2) c =
        QuotientGroup.mk' (derivedSeries X 2) y :=
      (mk_eq_mk_of_commute hS hy' hc hy'c).symm.trans hyy'mk.symm
    exact hfib h

theorem orderOf_mul_mul_eq_four_of_mk_ne (hS : Setup X E) {y y' c : X} (hy : y ∈ E)
    (hy' : y' ∈ E) (hc : c ∈ E) (hyy' : Commute y y') (hne : y ≠ y')
    (hfib : QuotientGroup.mk' (derivedSeries X 2) c ≠ QuotientGroup.mk' (derivedSeries X 2) y) :
    orderOf (y * y' * c) = 4 := by
  let φ : X →* X ⧸ derivedSeries X 2 := QuotientGroup.mk' (derivedSeries X 2)
  change φ c ≠ φ y at hfib
  have htri : IsTriangle E y c y' :=
    isTriangle_of_mk_ne hS hy hy' hc hyy' hne hfib
  have huv : φ y = φ y' := mk_eq_mk_of_commute hS hy hy' hyy'
  have hodd : Odd (orderOf (φ y * φ c)) := by
    have h := odd_orderOf_mk_mul hS hy hc
    change Odd (orderOf (φ (y * c))) at h
    rwa [map_mul] at h
  have hcc : φ c * φ c = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one hc, map_one]
  have hne1 : φ y * φ c ≠ 1 := by
    intro h1
    exact hfib ((eq_inv_of_mul_eq_one_left h1).trans
      (inv_eq_of_mul_eq_one_right hcc)).symm
  have hlt : 1 < orderOf (φ y * φ c) :=
    Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨(orderOf_pos _).ne', fun h => hne1 (orderOf_eq_one_iff.mp h)⟩
  exact CFSG.OddTranspositions.PartThree.orderOf_mul_eq_four_of_map_eq hS.oddT hS.normal
    htri φ huv hodd hlt

theorem commute_conj_of_mk_ne (hS : Setup X E) {y y' c : X} (hy : y ∈ E) (hy' : y' ∈ E)
    (hc : c ∈ E) (hyy' : Commute y y')
    (hfib : QuotientGroup.mk' (derivedSeries X 2) c ≠ QuotientGroup.mk' (derivedSeries X 2) y) :
    Commute ((y * y') * c * (y * y')⁻¹) c := by
  by_cases h_eq : y = y'
  · subst h_eq
    have h2 : y * y = 1 := hS.oddT.mul_self_eq_one hy
    simp [h2]
  · let t := y * y'
    have ht2 : t * t = 1 := by
      dsimp [t]
      rw [← pow_two, hyy'.mul_pow 2, pow_two y, pow_two y',
        hS.oddT.mul_self_eq_one hy, hS.oddT.mul_self_eq_one hy', mul_one]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h4 : orderOf (t * c) = 4 := by
      simpa [t] using orderOf_mul_mul_eq_four_of_mk_ne hS hy hy' hc hyy' h_eq hfib
    have hc2 : c * c = 1 := hS.oddT.mul_self_eq_one hc
    have hu2 : (t * c * t⁻¹) * (t * c * t⁻¹) = 1 := by
      rw [show (t * c * t⁻¹) * (t * c * t⁻¹) = t * (c * c) * t⁻¹ by group,
        hc2, mul_one, mul_inv_cancel]
    have huc : (t * c * t⁻¹) * c = (t * c) ^ 2 := by
      rw [htinv, pow_two]
      group
    have hpow4 : (t * c) ^ 4 = (t * c) ^ 2 * (t * c) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_two]
    have hsq : ((t * c * t⁻¹) * c) * ((t * c * t⁻¹) * c) = 1 := by
      rw [huc, ← hpow4, ← h4, pow_orderOf_eq_one]
    have hsq' : (t * c * t⁻¹ * c) ^ 2 = 1 := by simpa [pow_two] using hsq
    simpa [t] using (commute_iff_mul_sq_eq_one hu2 hc2).mpr hsq'

theorem exists_conj_eq_of_mk_ne (h86 : Lemma8_6) (hS : Setup X E) {y y' c : X} (hy : y ∈ E)
    (hy' : y' ∈ E) (hc : c ∈ E) (hyy' : Commute y y') (hne : y ≠ y')
    (hfib : QuotientGroup.mk' (derivedSeries X 2) c ≠ QuotientGroup.mk' (derivedSeries X 2) y) :
    ∃ c' ∈ E, Commute c c' ∧ c' ≠ c ∧ (c' * c) * y' * (c' * c)⁻¹ = y := by
  let φ : X →* X ⧸ derivedSeries X 2 := QuotientGroup.mk' (derivedSeries X 2)
  change φ c ≠ φ y at hfib
  have hyy'mk : φ y = φ y' := mk_eq_mk_of_commute hS hy hy' hyy'
  have hfib' : φ c ≠ φ y' := fun h => hfib (h.trans hyy'mk.symm)
  have htri : IsTriangle E y' c y :=
    isTriangle_of_mk_ne hS hy' hy hc hyy'.symm hne.symm hfib'
  have h4 : orderOf (y' * y * c) = 4 := by
    have h4' : orderOf (y * y' * c) = 4 :=
      orderOf_mul_mul_eq_four_of_mk_ne hS hy hy' hc hyy' hne hfib
    rwa [hyy'.eq] at h4'
  have hsolv : Group.IsSolvable (Subgroup.closure ({y', c, y} : Set X)) :=
    h86 X E hS.normal hS.oddT y' c y htri h4
  have hXK : Subgroup.closure ({y', c} : Set X) ≤
      Subgroup.closure ({y', c, y} : Set X) :=
    Subgroup.closure_mono (by intro z hz; rcases hz with rfl | rfl <;> simp)
  have hno : ∀ x ∈ E, x ∈ Subgroup.closure ({y', c} : Set X) →
      IsTriangle E y' x y → ¬ IsThirdKind y' x y := by
    intro x _ hxX htriX
    exact CFSG.OddTranspositions.PartThree.not_isThirdKind_of_solvable_subgroup
      hS.oddT hS.normal hsolv (Subgroup.subset_closure (by simp)) (hXK hxX)
      (Subgroup.subset_closure (by simp)) htriX
  have S : CFSG.Timmesfeld.Bridge.SecondKindStructure y' c y :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hS.oddT hS.normal htri h4 hno
  have hc2 : c * c = 1 := hS.oddT.mul_self_eq_one hc
  obtain ⟨x, hxQ, hxu⟩ := S.conj
  obtain ⟨q, hqQ, hqx⟩ := CFSG.GroupTheory.exists_eq_commutator_of_mem_commutator_zpowers hc2
    S.comm (fun q hq => S.normal c (Subgroup.subset_closure (by simp)) q hq) hxQ
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right (S.sq q hqQ)
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hx_eq : x = (q * c * q⁻¹) * c := by
    rw [hqx, commutatorElement_def, hqinv, hcinv]
  have hcK : c ∈ Subgroup.closure ({y', c, y} : Set X) :=
    Subgroup.subset_closure (by simp)
  have hcomm : Commute c (q * c * q⁻¹) := by
    have hcqmem : c * q * c⁻¹ ∈ CFSG.Timmesfeld.Bridge.conjClosure
        (Subgroup.closure {y', c}) (y' * y) := S.normal c hcK q hqQ
    have hcq : Commute (c * q * c⁻¹) q :=
      S.comm _ hcqmem _ hqQ
    rw [hcinv] at hcq
    show c * (q * c * q⁻¹) = (q * c * q⁻¹) * c
    rw [hqinv]
    calc c * (q * c * q) = (c * q * c) * q := by group
      _ = q * (c * q * c) := hcq.eq
      _ = (q * c * q) * c := by group
  refine ⟨q * c * q⁻¹, hS.normal q c hc, hcomm, ?_, ?_⟩
  · intro hc'eq
    have hx1 : x = 1 := by rw [hx_eq, hc'eq, hc2]
    have hy'eq : y' = y := by simpa [hx1] using hxu
    exact hne hy'eq.symm
  · rw [hx_eq] at hxu
    exact hxu

end CFSG.OddTranspositions.PartThree.EightEight
