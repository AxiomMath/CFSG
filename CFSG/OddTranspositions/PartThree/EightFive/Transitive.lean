module

public import CFSG.OddTranspositions.SevenThreeTransitive
public import CFSG.OddTranspositions.DeltaCentSet
public import CFSG.OddTranspositions.AscTheoremTwo
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.Timmesfeld.Bridge.Asc72ConjOrbit
public import CFSG.Timmesfeld.Bridge.OddTranspDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import Certificates.Certificate113

import CFSG.OddTranspositions.PartThree.EightFour
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.OddTranspositions.SixEight
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem conjOrbit_subset_centSet (hN : IsNormalSet D) {z u : G}
    (hu : u ∈ centSet D z) : conjOrbit (localGroup D z) u ⊆ centSet D z := by
  rintro x ⟨m, hm, rfl⟩
  have hmz : Commute m z := commute_of_mem_localGroup hm
  have h : Commute (m * u * m⁻¹) (m * z * m⁻¹) := hu.2.conj m
  have hz : m * z * m⁻¹ = z := by rw [hmz.eq]; group
  refine ⟨hN m u hu.1, ?_⟩
  rw [hz] at h
  exact h

omit [Finite G] in
theorem mem_conjOrbit_of_third_kind (hS : Setup G D) {u w v : G}
    (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) :
    v ∈ conjOrbit (localGroup D ((u * v * w) ^ n)) u ∧
      w ∈ conjOrbit (localGroup D ((u * v * w) ^ n)) u := by
  classical
  let z : G := (u * v * w) ^ n
  obtain ⟨-, -, hzu, hzv, hzw, -⟩ :=
    IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  have huC : u ∈ centSet D z := ⟨htri.1, hzu.symm⟩
  have hvC : v ∈ centSet D z := ⟨htri.2.1, hzv.symm⟩
  have hwC : w ∈ centSet D z := ⟨htri.2.2.1, hzw.symm⟩
  have huw : ¬ Commute u w := htri.2.2.2.2.2.1
  have hvw : ¬ Commute v w := htri.2.2.2.2.2.2
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one htri.1
  have hv2 : v * v = 1 := hS.oddT.mul_self_eq_one htri.2.1
  have hw2 : w * w = 1 := hS.oddT.mul_self_eq_one htri.2.2.1
  have hodduw : Odd (orderOf (u * w)) := hS.oddT.odd_of_not_commute htri.1 htri.2.2.1 huw
  have hoddvw : Odd (orderOf (v * w)) := hS.oddT.odd_of_not_commute htri.2.1 htri.2.2.1 hvw
  obtain ⟨gu, hgu, hguw⟩ := exists_conj_of_odd_orderOf_mul hu2 hw2 hodduw
  have huwK : Subgroup.closure ({u, w} : Set G) ≤ localGroup D z := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact mem_localGroup_of_mem huC
    · exact mem_localGroup_of_mem hwC
  have hwO : w ∈ conjOrbit (localGroup D z) u := ⟨gu, huwK hgu, hguw.symm⟩
  obtain ⟨gv, hgv, hgvw⟩ := exists_conj_of_odd_orderOf_mul hv2 hw2 hoddvw
  have hvwK : Subgroup.closure ({v, w} : Set G) ≤ localGroup D z := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact mem_localGroup_of_mem hvC
    · exact mem_localGroup_of_mem hwC
  have hvO : v ∈ conjOrbit (localGroup D z) u := by
    have h := conj_mem_conjOrbit (Subgroup.inv_mem _ (hvwK hgv)) hwO
    rwa [show gv⁻¹ * w * (gv⁻¹)⁻¹ = v by rw [← hgvw]; group] at h
  exact ⟨hvO, hwO⟩

theorem transitive_or_exists_commute (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z) :
    (∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x) ∨
      ∃ d ∈ D, Commute d u ∧ Commute d v ∧ Commute d w := by
  subst hzdef
  classical
  obtain ⟨-, -, hzu, -, -, -⟩ :=
    IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  have huC : u ∈ centSet D ((u * v * w) ^ n) := ⟨htri.1, hzu.symm⟩
  obtain ⟨hvO, hwO⟩ := mem_conjOrbit_of_third_kind hS htri hn hord
  by_cases hT : ∀ x ∈ centSet D ((u * v * w) ^ n),
      ∃ k ∈ localGroup D ((u * v * w) ^ n), k * u * k⁻¹ = x
  · exact Or.inl hT
  · right
    push Not at hT
    obtain ⟨x, hx, hxnot⟩ := hT
    have hxO : x ∉ conjOrbit (localGroup D ((u * v * w) ^ n)) u := by
      rintro ⟨k, hk, hkx⟩
      exact hxnot k hk hkx.symm
    have hΔu : conjOrbit (localGroup D ((u * v * w) ^ n)) u ⊆
        Delta D ((u * v * w) ^ n) := by
      rw [Delta_eq_centSet]
      exact conjOrbit_subset_centSet hS.normal huC
    have hΔx : conjOrbit (localGroup D ((u * v * w) ^ n)) x ⊆
        Delta D ((u * v * w) ^ n) := by
      rw [Delta_eq_centSet]
      exact conjOrbit_subset_centSet hS.normal hx
    have hcomm := thirdK_orbits_commute hS hΔu hΔx
      (fun k hk y hy => by
        rw [thirdK_eq_localGroup] at hk
        exact conj_mem_conjOrbit hk hy)
      (fun k hk y hy => by
        rw [thirdK_eq_localGroup] at hk
        exact conj_mem_conjOrbit hk hy)
      (disjoint_conjOrbit_of_not_mem hxO)
    exact ⟨x, hx.1,
      (hcomm u (self_mem_conjOrbit _ u) x (self_mem_conjOrbit _ x)).symm,
      (hcomm v hvO x (self_mem_conjOrbit _ x)).symm,
      (hcomm w hwO x (self_mem_conjOrbit _ x)).symm⟩

omit [Finite G] in
theorem transitive_pair_of_transitive {z u : G}
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x) :
    ∀ x ∈ centSet D z, ∀ y ∈ centSet D z, ∃ h ∈ localGroup D z, h * x * h⁻¹ = y := by
  intro x hx y hy
  obtain ⟨k₁, hk₁, hk₁x⟩ := htrans x hx
  obtain ⟨k₂, hk₂, hk₂y⟩ := htrans y hy
  refine ⟨k₂ * k₁⁻¹, Subgroup.mul_mem _ hk₂ (Subgroup.inv_mem _ hk₁), ?_⟩
  calc (k₂ * k₁⁻¹) * x * (k₂ * k₁⁻¹)⁻¹ = k₂ * (k₁⁻¹ * x * k₁) * k₂⁻¹ := by group
    _ = k₂ * (k₁⁻¹ * (k₁ * u * k₁⁻¹) * k₁) * k₂⁻¹ := by rw [hk₁x]
    _ = k₂ * u * k₂⁻¹ := by group
    _ = y := hk₂y

theorem exists_commute_of_pCore_le_center
    (h2 : AschbacherTheoremTwo) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hQ : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z))) :
    ∃ d ∈ D, Commute d u ∧ Commute d v ∧ Commute d w := by
  subst hzdef
  have htrans' := transitive_pair_of_transitive (z := (u * v * w) ^ n) (u := u) htrans
  rcases lemma8_4 h2 hC.setup hC hrad htri hn hn1 hord htrans' hQ hB with hzD | hO4'
  · obtain ⟨-, -, hzu, hzv, hzw, -⟩ :=
      IsTriangle.third_kind hC.setup.oddT hC.setup.normal htri hn hord
    exact ⟨(u * v * w) ^ n, hzD, hzu, hzv, hzw⟩
  · exact (hO4 hO4').elim

end CFSG.OddTranspositions.PartThree
