module

public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
import CFSG.RankThree.GF2n.Tim81.Sec5.HBarAut
import CFSG.RankThree.GF2n.Tim81.Sec5.S53S55
import CFSG.Quasithin.EmptyFaithful.T1521SBlkThree
import CFSG.GroupTheory.OddOrderPGroup

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

private theorem fSet_V_le {A : Subgroup G} (hA : A ∈ fSet M V) : V ≤ A := by
  obtain ⟨-, -, U₀, -, x₀, -, hAeq⟩ := hA
  rw [hAeq]
  exact le_sup_left

private theorem fSet_not_mem_V (h : RootHyp M V) : V ∉ fSet M V := by
  intro hV
  have hcard : Nat.card V = Nat.card V ^ 2 := hV.2.1
  have h2 : Nat.card V * 1 = Nat.card V * Nat.card V := by
    rw [mul_one, ← pow_two, ← hcard]
  have hq : 1 = Nat.card V := Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  have h4 := h.four_le_card
  omega

private theorem fSet_not_mem_commutator (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) : ⁅Pc M V, U⁆ ∉ fSet M V := by
  intro hE
  have hcard : Nat.card V ^ 3 = Nat.card V ^ 2 := by
    rw [← hS.card_commutator_Pc hU, hE.2.1]
  have h2 : Nat.card V ^ 2 * Nat.card V = Nat.card V ^ 2 * 1 := by
    rw [mul_one, show Nat.card V ^ 2 * Nat.card V = Nat.card V ^ 3 by ring]
    exact hcard
  have hq : Nat.card V = 1 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos Nat.card_pos) h2
  have h4 := hS.toRootHyp.four_le_card
  omega

private theorem inf_centralizer_trichotomy (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V) :
    ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) = V ∨
      ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) ∈ fSet M V ∨
      ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) = ⁅Pc M V, U⁆ := by
  classical
  have hCE : Pc M V ⊓ Subgroup.centralizer (U' : Set G) =
      Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G) :=
    hS.Pc_inf_centralizer_eq_commutator hU'
  refine hS.eq_V_or_mem_fSet_or_eq_commutator hU ?_ inf_le_left ?_
  · refine le_inf (hS.V_le_commutator hU) ?_
    rw [hCE]
    obtain ⟨-, -, -, -, -, -, hVC', -⟩ := hS.commutator_facts_of_mem_sigmaSet hU'
    exact hVC'
  · intro x hx hxV
    obtain ⟨hxE, hxC'⟩ := Subgroup.mem_inf.mp hx
    have hxCE : x ∈ Pc M V ⊓ Subgroup.centralizer
        ((⁅Pc M V, U'⁆ : Subgroup G) : Set G) := hCE ▸ hxC'
    obtain ⟨-, hxC'E⟩ := Subgroup.mem_inf.mp hxCE
    obtain ⟨B, hB, hxB, hBE⟩ := hS.stmt52a U hU x hxE
    have h51b := hS.stmt51b B hB x hxB hxV
    have hE'le : ⁅Pc M V, U'⁆ ≤ Pc M V ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine le_inf (hS.commutator_le_Pc hU') ?_
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (Subgroup.mem_centralizer_iff.mp hxC'E e he).symm
    rw [h51b] at hE'le
    have hBC : B ≤ Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hE'le he)).2 b hb).symm
    refine ⟨B, hB, hxB, ?_⟩
    rw [hCE]
    exact le_inf hBE (le_inf hB.1 hBC)

private theorem commutator_le_inf (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hA : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) ∈ fSet M V) :
    ⁅⁅Pc M V, U'⁆, U⁆ ≤
      ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) := by
  classical
  obtain ⟨g, y, hSg, hyH, hUeq, hVy, -, hEW, hCK, -⟩ := hS.exists_sigma_data hU
  set A : Subgroup G := ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) with hAdef
  have hCE : Pc M V ⊓ Subgroup.centralizer (U' : Set G) =
      Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G) :=
    hS.Pc_inf_centralizer_eq_commutator hU'
  have hAleW : A ≤ Tim79a.xOf V (hOf M V g) := by
    refine (inf_le_left.trans ?_)
    rw [hEW]
    exact inf_le_right
  have hAleC : A ≤ Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G) := by
    refine (inf_le_right.trans ?_)
    rw [hCE]
    exact inf_le_right
  rw [Subgroup.commutator_le]
  intro e he u hu
  by_cases heC : e ∈ Pc M V ⊓ Subgroup.centralizer (U : Set G)
  · have h1 : ⁅e, u⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp heC).2 u hu).symm
    rw [h1]
    exact A.one_mem
  · have heP : e ∈ Pc M V := hS.commutator_le_Pc hU' he
    have heK : e ∉ kOf V (hOf M V g) := fun hK =>
      heC (hCK ▸ Subgroup.mem_inf.mpr ⟨heP, hK⟩)
    have huW : u ∈ Tim79a.xOf V (hOf M V g) :=
      conjSubgroup_le_xOf_of_mem hyH (hVy ▸ hUeq ▸ hu)
    have hc1 : ⁅⁅u, e⁆, e⁆ = 1 :=
      Sec45Shape.commutator_commutator_eq_one hS.toRootHyp hSg heP huW
    have hcW : ⁅u, e⁆ ∈ Tim79a.xOf V (hOf M V g) := by
      have hxN : e ∈ Subgroup.normalizer (Tim79a.xOf V (hOf M V g) : Set G) :=
        Tim79a.H_le_normalizer_xOf V (hOf M V g) (hSg.Pc_le heP)
      have h1 : e * u * e⁻¹ ∈ Tim79a.xOf V (hOf M V g) :=
        (Subgroup.mem_normalizer_iff.mp hxN u).mp huW
      have h2 : ⁅u, e⁆ = u * (e * u * e⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact (Tim79a.xOf V (hOf M V g)).mul_mem huW
        ((Tim79a.xOf V (hOf M V g)).inv_mem h1)
    have hmem : ⁅u, e⁆ ∈ Tim79a.xOf V (hOf M V g) ⊓
        Subgroup.centralizer ({e} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hcW, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (commutatorElement_eq_one_iff_mul_comm.mp hc1).symm
    have hcard := (Sec45Shape.xOf_inf_centralizer_le_and_card hS.toRootHyp hSg heP heK).2
    have hAeq : A = Tim79a.xOf V (hOf M V g) ⊓ Subgroup.centralizer ({e} : Set G) := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · refine le_inf hAleW ?_
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact Subgroup.mem_centralizer_iff.mp (hAleC ha) e he
      · rw [hcard, hA.2.1]
    have hmemA : ⁅u, e⁆ ∈ A := hAeq.symm ▸ hmem
    rw [show ⁅e, u⁆ = ⁅u, e⁆⁻¹ from (commutatorElement_inv (g₁ := u) (g₂ := e)).symm]
    exact A.inv_mem hmemA

private theorem le_normalizer_sup_commutator {U U' : Subgroup G} :
    U' ≤ Subgroup.normalizer ((U ⊔ ⁅U, U'⁆ : Subgroup G) : Set G) := by
  classical
  let D : Subgroup G := ⁅U, U'⁆
  have hDU : D ≤ U ⊔ D := le_sup_right
  have hDN : ∀ u' ∈ U', conjSubgroup u' D = D := fun u' hu' =>
    conjSubgroup_eq_self_iff.mpr (Subgroup.normalizer_commutator_ge_right U U' hu')
  have hUconj : ∀ u' ∈ U', conjSubgroup u' U ≤ U ⊔ D := by
    intro u' hu' x hx
    have hx' : x ∈ U.map (MulAut.conj u').toMonoidHom := hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx'
    have hcomm : ⁅u', u⁆ ∈ D := by
      have h := Subgroup.commutator_mem_commutator hu' hu
      rwa [Subgroup.commutator_comm U' U] at h
    have hmul : u' * u * u'⁻¹ = ⁅u', u⁆ * u := by
      rw [commutatorElement_def]
      group
    change u' * u * u'⁻¹ ∈ U ⊔ D
    rw [hmul]
    exact (U ⊔ D).mul_mem ((le_sup_right : D ≤ U ⊔ D) hcomm)
      ((le_sup_left : U ≤ U ⊔ D) hu)
  intro u' hu'
  rw [mem_normalizer_iff_conjSubgroup_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · calc conjSubgroup u' (U ⊔ D) = conjSubgroup u' U ⊔ conjSubgroup u' D :=
        conjSubgroup_sup u' U D
      _ ≤ U ⊔ D := sup_le (hUconj u' hu') (by rw [hDN u' hu']; exact hDU)
  · rw [card_conjSubgroup]

private theorem isPGroup_sup_of_mem_fSet (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {A B : Subgroup G}
    (hA : A ∈ fSet M V) (hB : B ∈ fSet M V) :
    IsPGroup 2 ↥(A ⊔ B) ∧ Pc M V ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  classical
  have hAP : A ≤ Pc M V := hA.1
  have hBP : B ≤ Pc M V := hB.1
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hA2 : IsPGroup 2 A := hP2.to_le hAP
  have hB2 : IsPGroup 2 B := hP2.to_le hBP
  have hPA : Pc M V ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono_right hAP).trans
        ((le_of_eq (hS.commutator_Pc_eq_V ⟨U, hU⟩)).trans (fSet_V_le hA)))
  have hPB : Pc M V ≤ Subgroup.normalizer (B : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr
      ((Subgroup.commutator_mono_right hBP).trans
        ((le_of_eq (hS.commutator_Pc_eq_V ⟨U, hU⟩)).trans (fSet_V_le hB)))
  exact ⟨hA2.to_sup_of_normal_right' hB2 (hAP.trans hPB),
    (le_inf hPA hPB).trans (Subgroup.inf_normalizer_le_normalizer_sup A B)⟩

private theorem centralizes_sup_of_fSet {A B U U' W W' : Subgroup G}
    (hAW : A ≤ W) (hUW : U ≤ W) (hW : IsMulCommutative ↥W)
    (hBW : B ≤ W') (hU'W' : U' ≤ W') (hW' : IsMulCommutative ↥W')
    (hAC' : A ≤ Subgroup.centralizer (U' : Set G))
    (hBC : B ≤ Subgroup.centralizer (U : Set G)) :
    U ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) ∧
      U' ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hUCA : U ≤ Subgroup.centralizer (A : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (hW.is_comm.comm ⟨a, hAW ha⟩ ⟨u, hUW hu⟩)
  have hUCB : U ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.le_centralizer_iff.mpr hBC
  have hU'CA : U' ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff.mpr hAC'
  have hU'CB : U' ≤ Subgroup.centralizer (B : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hW'.is_comm.comm ⟨b, hBW hb⟩ ⟨u, hU'W' hu⟩)
  exact ⟨Subgroup.le_centralizer_iff.mpr
      (sup_le (Subgroup.le_centralizer_iff.mp hUCA) (Subgroup.le_centralizer_iff.mp hUCB)),
    Subgroup.le_centralizer_iff.mpr
      (sup_le (Subgroup.le_centralizer_iff.mp hU'CA) (Subgroup.le_centralizer_iff.mp hU'CB))⟩

private theorem isPGroup_commutator (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hA : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) ∈ fSet M V)
    (hB : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U : Set G)) ∈ fSet M V) :
    IsPGroup 2 ↥⁅U, U'⁆ := by
  classical
  obtain ⟨g, y, hSg, hyH, hUeq, hVy, -, hEW, hCK, -⟩ := hS.exists_sigma_data hU
  obtain ⟨g', y', hSg', hyH', hU'eq, hVy', -, hEW', hCK', -⟩ := hS.exists_sigma_data hU'
  set A : Subgroup G := ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) with hAdef
  set B : Subgroup G := ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U : Set G)) with hBdef
  have hAE : A ≤ ⁅Pc M V, U⁆ := inf_le_left
  have hBE' : B ≤ ⁅Pc M V, U'⁆ := inf_le_left
  have hAC' : A ≤ Pc M V ⊓ Subgroup.centralizer (U' : Set G) := inf_le_right
  have hBC : B ≤ Pc M V ⊓ Subgroup.centralizer (U : Set G) := inf_le_right
  have hUW : U ≤ Tim79a.xOf V (hOf M V g) := by
    intro u hu
    exact conjSubgroup_le_xOf_of_mem hyH (hVy ▸ hUeq ▸ hu)
  have hAW : A ≤ Tim79a.xOf V (hOf M V g) := by
    refine hAE.trans ?_
    rw [hEW]
    exact inf_le_right
  have hUW' : U' ≤ Tim79a.xOf V (hOf M V g') := by
    intro u hu
    exact conjSubgroup_le_xOf_of_mem hyH' (hVy' ▸ hU'eq ▸ hu)
  have hBW : B ≤ Tim79a.xOf V (hOf M V g') := by
    refine hBE'.trans ?_
    rw [hEW']
    exact inf_le_right
  obtain ⟨hUCN, hU'CN⟩ :=
    centralizes_sup_of_fSet hAW hUW (hSg.isElemAbelian hS.toRootHyp).1
      hBW hUW' (hSg'.isElemAbelian hS.toRootHyp).1 (hAC'.trans inf_le_right)
      (hBC.trans inf_le_right)
  obtain ⟨hN2, hPN⟩ := isPGroup_sup_of_mem_fSet hS hU hA hB
  have h1 : ⁅⁅U', Pc M V⁆, U⁆ ≤ A ⊔ B := by
    rw [Subgroup.commutator_comm U' (Pc M V)]
    exact (commutator_le_inf hS hU hU' hA).trans le_sup_left
  have h2 : ⁅⁅Pc M V, U⁆, U'⁆ ≤ A ⊔ B :=
    (commutator_le_inf hS hU' hU hB).trans le_sup_right
  have hDrotate : ⁅⁅U, U'⁆, Pc M V⁆ ≤ A ⊔ B :=
    CFSG.Quasithin.commutator_commutator_le_of_rotate1521
      (hUCN.trans (Subgroup.centralizer_le_normalizer _))
      (hU'CN.trans (Subgroup.centralizer_le_normalizer _)) hPN h1 h2
  refine CFSG.Quasithin.isPGroup_two_of_odd_orderOf_eq_one ?_
  intro x hxD hxodd
  have hxC : x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    (Subgroup.commutator_le_sup U U').trans (sup_le hUCN hU'CN) hxD
  have hxP : ∀ p ∈ Pc M V, ⁅x, p⁆ ∈ A ⊔ B := fun p hp =>
    hDrotate (Subgroup.commutator_mem_commutator hxD hp)
  have hxCV : x ∈ Subgroup.centralizer (Pc M V : Set G) :=
    CFSG.mem_centralizer_of_odd_pow_eq_one hN2 hxodd (pow_orderOf_eq_one x) hxC hxP
  have hxV : x ∈ V := by
    rw [← hS.toRootHyp.toHyp.centralizer_Pc]
    exact hxCV
  have hx2 : x * x = 1 :=
    hS.toRootHyp.toHyp.mul_self_eq_one_of_mem_conj (g := 1) (by
      rw [conjSubgroup_one]
      exact hxV)
  have hcop : Nat.Coprime (orderOf x) 2 := hxodd.coprime_two_right
  have hx1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (orderOf_dvd_of_pow_eq_one (by rwa [pow_two]))
  exact orderOf_eq_one_iff.mp hx1

private theorem isPGroup_sup (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hA : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) ∈ fSet M V)
    (hB : ⁅Pc M V, U'⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U : Set G)) ∈ fSet M V) :
    IsPGroup 2 ↥(U ⊔ U') := by
  have hD2 : IsPGroup 2 ↥⁅U, U'⁆ := isPGroup_commutator hS hU hU' hA hB
  have hU2 : IsPGroup 2 U := by
    obtain ⟨g, rfl, -⟩ := hU
    exact hS.toRootHyp.toHyp.isPGroup_V.map (MulAut.conj g).toMonoidHom
  have hU'2 : IsPGroup 2 U' := by
    obtain ⟨g, rfl, -⟩ := hU'
    exact hS.toRootHyp.toHyp.isPGroup_V.map (MulAut.conj g).toMonoidHom
  have hUD2 : IsPGroup 2 ↥(U ⊔ ⁅U, U'⁆) :=
    hU2.to_sup_of_normal_right' hD2 (Subgroup.normalizer_commutator_ge_left U U')
  have hU'N : U' ≤ Subgroup.normalizer ((U ⊔ ⁅U, U'⁆ : Subgroup G) : Set G) :=
    le_normalizer_sup_commutator (U := U) (U' := U')
  have htop : IsPGroup 2 ↥((U ⊔ ⁅U, U'⁆) ⊔ U') :=
    hUD2.to_sup_of_normal_left' hU'2 hU'N
  exact htop.to_le (sup_le (le_sup_of_le_left le_sup_left) le_sup_right)

private theorem conjSubgroup_hOf_eq_of_mem (h : Hyp M V) {g a : G} (haM : a ∈ M)
    (ha : conjSubgroup a (conjSubgroup g V) = conjSubgroup g V) :
    conjSubgroup a (hOf M V g) = hOf M V g := by
  have hconjV' : conjSubgroup (a * g) V = conjSubgroup g V := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact ha
  have hPfix : conjSubgroup a (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (h.le_normalizer_Pc haM)
  have hPconj : conjSubgroup a (conjSubgroup g (Pc M V)) = conjSubgroup g (Pc M V) := by
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact h.conjSubgroup_Pc_eq_of_conjSubgroup_eq hconjV'
  change conjSubgroup a (Pc M V ⊔ conjSubgroup g (Pc M V)) = Pc M V ⊔ conjSubgroup g (Pc M V)
  rw [conjSubgroup_sup, hPfix, hPconj]

private theorem exists_ne_one_mem_centralizer_xOf_of_commute (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V) (hbot : ⁅U, U'⁆ = ⊥)
    {g y : G} (hSg : Sec45Shape M V (hOf M V g) g) (hyH : y ∈ hOf M V g)
    (hUeq : U = conjSubgroup g V) (hVy : conjSubgroup g V = conjSubgroup y V) :
    ∃ b ∈ U', b ≠ 1 ∧ b ∈ Subgroup.centralizer (Tim79a.xOf V (hOf M V g) : Set G) := by
  classical
  have hM' : U' ≤ M := (hS.le_M_of_mem_sigmaSet hU').1
  have hCV' : U' ≤ Subgroup.centralizer (V : Set G) := (hS.le_M_of_mem_sigmaSet hU').2
  have hcentrU' : U' ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
  obtain ⟨g', hU'eq, -⟩ := hU'
  have hU'2 : ∀ a ∈ U', a * a = 1 := fun a ha =>
    hS.toRootHyp.toHyp.mul_self_eq_one_of_mem_conj (g := g') (hU'eq ▸ ha)
  have hU'c : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a := fun a ha b hb =>
    hS.toRootHyp.toHyp.commute_of_mem_conj (hU'eq ▸ ha) (hU'eq ▸ hb)
  have hU'card : 2 < Nat.card U' := by
    have h : Nat.card U' = Nat.card V := by rw [hU'eq, card_conjSubgroup]
    have h4 := hS.toRootHyp.four_le_card
    omega
  have hAH : ∀ a ∈ U', conjSubgroup a (hOf M V g) = hOf M V g := fun a ha => by
    refine conjSubgroup_hOf_eq_of_mem hS.toRootHyp.toHyp (hM' ha) ?_
    rw [← hUeq]
    exact conjSubgroup_eq_self_iff.mpr
      (Subgroup.centralizer_le_normalizer (U : Set G) (hcentrU' ha))
  have hne : conjSubgroup (1 : G) V ≠ conjSubgroup y V := by
    rw [conjSubgroup_one]
    intro h
    exact ne_of_mem_sigmaSet hS.toRootHyp hU (hUeq.trans (hVy.trans h.symm))
  have hA1 : ∀ a ∈ U', conjSubgroup a (conjSubgroup (1 : G) V) = conjSubgroup (1 : G) V := by
    intro a ha
    simp only [conjSubgroup_one]
    exact conjSubgroup_eq_self_iff.mpr
      (Subgroup.centralizer_le_normalizer (V : Set G) (hCV' ha))
  have hA2 : ∀ a ∈ U', conjSubgroup a (conjSubgroup y V) = conjSubgroup y V := by
    intro a ha
    have hyU : conjSubgroup y V = U := hVy.symm.trans hUeq.symm
    rw [hyU]
    exact conjSubgroup_eq_self_iff.mpr
      (Subgroup.centralizer_le_normalizer (U : Set G) (hcentrU' ha))
  exact Sec45Shape.exists_ne_one_mem_centralizer_xOf hS.toRootHyp hSg hU'2 hU'c hU'card hAH
    (x₁ := 1) (x₂ := y) (hOf M V g).one_mem hyH hne hA1 hA2

private theorem commutator_ne_bot_of_mem_fSet (hS : Sec5Hyp M V) {U U' : Subgroup G}
    (hU : U ∈ sigmaSet M V) (hU' : U' ∈ sigmaSet M V)
    (hA : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) ∈ fSet M V) :
    ⁅U, U'⁆ ≠ ⊥ := by
  classical
  intro hbot
  obtain ⟨g, y, hSg, hyH, hUeq, hVy, -, hEW, -, -⟩ := hS.exists_sigma_data hU
  obtain ⟨g', y', hSg', hyH', hU'eq, hVy', hyV', -, -, hCEK'⟩ := hS.exists_sigma_data hU'
  obtain ⟨b, hbU', hb1, hbW⟩ :=
    exists_ne_one_mem_centralizer_xOf_of_commute hS hU hU' hbot hSg hyH hUeq hVy
  have hbU'y : b ∈ conjSubgroup y' V := hVy' ▸ (hU'eq ▸ hbU')
  have hE_le : ⁅Pc M V, U⁆ ≤ Pc M V ⊓ kOf V (hOf M V g') := by
    refine le_inf (hS.commutator_le_Pc hU) ?_
    intro e he
    have heW : e ∈ Tim79a.xOf V (hOf M V g) :=
      (Subgroup.mem_inf.mp (hEW ▸ he)).2
    have h1 : ⁅e, b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hbW e heW)
    have h2 : ⁅e, b⁆ ∈ V := by
      rw [h1]
      exact V.one_mem
    exact Sec45Shape.mem_kOf_of_commutator_mem hS.toRootHyp hSg' hyH' hyV' hbU'y hb1
      (hS.commutator_le_Pc hU he) h2
  have hAE : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) = ⁅Pc M V, U⁆ := by
    refine le_antisymm inf_le_left ?_
    refine le_inf le_rfl ?_
    rw [hS.Pc_inf_centralizer_eq_commutator hU', hCEK']
    exact hE_le
  have hcard : Nat.card V ^ 2 = Nat.card V ^ 3 := by
    rw [← hA.2.1, hAE, hS.card_commutator_Pc hU]
  have h2 : Nat.card V ^ 2 * Nat.card V = Nat.card V ^ 2 * 1 := by
    rw [mul_one, show Nat.card V ^ 2 * Nat.card V = Nat.card V ^ 3 by ring]
    exact hcard.symm
  have hq : Nat.card V = 1 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos Nat.card_pos) h2
  have h4 := hS.toRootHyp.four_le_card
  omega

theorem Sec5Hyp.stmt57 (hS : Sec5Hyp M V)
    (h56 : ∀ M' V' : Subgroup G, Sec5Hyp M' V' → Sec5.Stmt56 M' V') :
    Sec5.Stmt57 M V := by
  intro U hU U' hU'
  have hCE : Pc M V ⊓ Subgroup.centralizer (U : Set G) =
      Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G) :=
    hS.Pc_inf_centralizer_eq_commutator hU
  have hCE' : Pc M V ⊓ Subgroup.centralizer (U' : Set G) =
      Pc M V ⊓ Subgroup.centralizer ((⁅Pc M V, U'⁆ : Subgroup G) : Set G) :=
    hS.Pc_inf_centralizer_eq_commutator hU'
  rcases inf_centralizer_trichotomy hS hU hU' with hV | hF | hE
  · right
    left
    exact ⟨hV, h56 M V hS U hU U' hU' ((hS.cap_symm hU hU').mpr (hCE' ▸ hV))⟩
  · right
    right
    rcases inf_centralizer_trichotomy hS hU' hU with hBV | hBF | hBE
    · have hAV : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) = V :=
        hCE'.symm ▸ ((hS.cap_symm hU hU').mp (hCE ▸ hBV))
      rw [hAV] at hF
      exact absurd hF (fSet_not_mem_V hS.toRootHyp)
    · exact ⟨hF, isPGroup_sup hS hU hU' hF hBF, commutator_ne_bot_of_mem_fSet hS hU hU' hF⟩
    · have hE'le : ⁅Pc M V, U'⁆ ≤ Pc M V ⊓ Subgroup.centralizer (U : Set G) :=
        hBE ▸ inf_le_right
      have hE'CE : ⁅Pc M V, U'⁆ ≤
          Subgroup.centralizer ((⁅Pc M V, U⁆ : Subgroup G) : Set G) := by
        refine hE'le.trans ?_
        rw [hCE]
        exact inf_le_right
      have hAE : ⁅Pc M V, U⁆ ⊓ (Pc M V ⊓ Subgroup.centralizer (U' : Set G)) =
          ⁅Pc M V, U⁆ := by
        refine le_antisymm inf_le_left ?_
        refine le_inf le_rfl ?_
        rw [hCE']
        exact le_inf (hS.commutator_le_Pc hU) (Subgroup.le_centralizer_iff.mpr hE'CE)
      rw [hAE] at hF
      exact absurd hF (fSet_not_mem_commutator hS hU)
  · left
    refine ⟨hE ▸ inf_le_right, ?_⟩
    refine hS.stmt53 U hU U' hU' ?_
    rw [← hCE']
    exact hE ▸ inf_le_right

end CFSG.RankThree.GF2n.Tim81

end
