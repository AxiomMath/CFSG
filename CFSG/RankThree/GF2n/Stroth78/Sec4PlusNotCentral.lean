module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

import CFSG.RankThree.GF2n.Stroth78.Sec2Fifteen
import CFSG.RankThree.GF2n.Stroth78.Sec2Eleven
import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenReverse

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_not_commute_of_mem_centerIn_QaOf (S : Setting z E F) {a s : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z)
    (hzaZ : z ∉ centerIn (QaOf a))
    (hsZ : s ∈ centerIn (QaOf a)) (hsH : s ∈ H z) (hs2 : s ^ 2 = 1) (hsQ : s ∉ Q z) :
    ∃ q ∈ Q z ⊓ Subgroup.centralizer ({a} : Set G), s * q ≠ q * s := by
  by_contra hcon
  push Not at hcon
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hq : (qS S).polarBilin.Nondegenerate := by
    letI := modAbF S
    exact q_nondegenerate S
  have h2 := finrank_commSpace_eq_two S haQ hconj haZ hzaZ hsZ hsH hs2 hsQ
  have hle : LinearMap.BilinForm.orthogonal (qS S).polarBilin
      (Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)}) ≤
      fixSpace (conjQbar S ⟨s, hsH⟩) := by
    rw [← QaInterImage_CQ_eq_orthogonal S haQ]
    intro v hv
    rw [mem_QaInterImage_iff] at hv
    obtain ⟨y, hyC, hyv⟩ := hv
    have hv' : v = Additive.ofMul (mkQbar S y) := (congrArg Additive.ofMul hyv).symm
    rw [mem_fixSpace, hv']
    have h1 := additive_commutator_eq_sub S hsH y.2
    have hcomm : ⁅(y : G), s⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hcon y hyC).symm
    have hone : (⟨⁅(y : G), s⁆, commutator_mem_Q_of_mem_H hsH y.2⟩ : ↥(Q z)) = 1 :=
      Subtype.ext hcomm
    rw [hone, map_one] at h1
    exact (sub_eq_zero.mp h1.symm)
  have hne0 : Additive.ofMul (mkQbar S ⟨a, haQ⟩) ≠ 0 := aV_ne_zero S haQ haZ
  have hspan : finrank (ZMod 2)
      (Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)}) = 1 :=
    finrank_span_singleton hne0
  have horth := LinearMap.BilinForm.finrank_orthogonal hq
    (Submodule.span (ZMod 2) {Additive.ofMul (mkQbar S ⟨a, haQ⟩)})
  have hmono := Submodule.finrank_mono hle
  have hsum := finrank_commSpace_add_finrank_fixSpace (conjQbar S ⟨s, hsH⟩)
  have hpos : 0 < finrank (ZMod 2) (Additive (QbarOf S)) :=
    Module.finrank_pos_iff.mpr ⟨⟨Additive.ofMul (mkQbar S ⟨a, haQ⟩), 0, hne0⟩⟩
  omega

theorem commute_of_mem_centerIn_QaOf_of_le_centerIn_H (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hZZ : ZQ z ≤ centerIn (H z)) {s y : G} (hs : s ∈ centerIn (QaOf a))
    (hy : y * a = a * y) : s * y = y * s := by
  obtain ⟨g, hgQaz, hga⟩ :=
    exists_conj_eq_z_of_mem_QaOf_mul_z S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
  have hgz : g * z * g⁻¹ = a := conj_z_eq_of_conj_a_eq S h.mem_Q h.isConj h.not_mem_ZQ hgQaz hga
  rw [centerIn_QaOf_eq_map_of_conj_eq S hgz] at hs
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hs
  have hrH : r ∈ centerIn (H z) := hZZ hr
  have hy'H : g⁻¹ * y * g ∈ H z := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    have hy2 : y * (g * z * g⁻¹) = (g * z * g⁻¹) * y := by rw [hgz]; exact hy
    calc z * (g⁻¹ * y * g) = g⁻¹ * ((g * z * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [hy2]
      _ = g⁻¹ * y * g * z := by group
  have hr' : (g⁻¹ * y * g) * r = r * (g⁻¹ * y * g) :=
    Subgroup.mem_centralizer_iff.mp hrH.2 _ hy'H
  change g * r * g⁻¹ * y = y * (g * r * g⁻¹)
  calc g * r * g⁻¹ * y = g * (r * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * r) * g⁻¹ := by rw [hr']
    _ = y * (g * r * g⁻¹) := by group

theorem not_zq_le_centerIn_H (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w) :
    ¬ ZQ z ≤ centerIn (H z) := by
  intro hZZ
  obtain ⟨s, hsZ, hsQ⟩ := Set.not_subset.mp h.centerIn_Qa_not_le_Q
  have hsH : s ∈ H z := centerIn_QaOf_le_H S h.mem_Qa hsZ
  have hs2 : s ^ 2 = 1 := sq_eq_one_of_mem_centerIn_QaOf S h.isConj hsZ
  have hzaZ : z ∉ centerIn (QaOf a) :=
    z_not_mem_centerIn_Qa S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
  obtain ⟨q, hq, hne⟩ := exists_not_commute_of_mem_centerIn_QaOf S h.mem_Q h.isConj
    h.not_mem_ZQ hzaZ hsZ hsH hs2 hsQ
  have hqa : q * a = a * q :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hq).2 a (Set.mem_singleton a)).symm
  exact hne (commute_of_mem_centerIn_QaOf_of_le_centerIn_H S h hZZ hsZ hqa)

end CFSG.RankThree.GF2n.Stroth78
