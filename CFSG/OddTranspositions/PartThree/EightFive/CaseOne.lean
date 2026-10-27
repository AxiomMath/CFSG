module

public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCore
public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralBlocks
public import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.SixSeven
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
import CFSG.OddTranspositions.BlockAction2
import CFSG.OddTranspositions.SecondKindCoset

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem conj_pCore_not_mem_alpha_mem_D_and_commute (hC : HypothesisC D)
    {w v : G} (htri : IsTriangle D hC.d w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (hC.d * v * w) = 2 * n) {z : G} (hzdef : (hC.d * v * w) ^ n = z)
    {q : localGroup D z} (hq : q ∈ CFSG.pCore 2 (localGroup D z))
    (hqa : (q : G) * hC.d * (q : G)⁻¹ ∉ hC.alpha) :
    (q : G) * hC.d * (q : G)⁻¹ ∈ D ∧
      Commute ((q : G) * hC.d * (q : G)⁻¹) hC.d := by
  classical
  have hS := hC.setup
  set u : G := hC.d with hu_def
  have htri_u : IsTriangle D u w v := by simpa [hu_def] using htri
  have hord_u : orderOf (u * v * w) = 2 * n := by simpa [hu_def] using hord
  have hzdef_u : (u * v * w) ^ n = z := by simpa [hu_def] using hzdef
  have halpha_d : u ∈ hC.alpha := by rw [hu_def]; exact hC.d_mem_alpha
  set a : G := (q : G) * u * (q : G)⁻¹ with ha_def
  have hadef : (q : G) * u * (q : G)⁻¹ = a := ha_def.symm
  have hqa_u : a ∉ hC.alpha := by simpa [ha_def, hu_def] using hqa
  obtain ⟨huC, -, -, -⟩ := thirdKind_mem_centSet hS htri_u hn hord_u
  rw [hzdef_u] at huC
  have haD : a ∈ D := by
    rw [ha_def]
    exact hS.conj_mem (q : G) htri_u.1
  have haumemK : a * u⁻¹ ∈ (CFSG.pCore 2 (localGroup D z)).map
      (localGroup D z).subtype :=
    conj_mul_inv_mem_pCore (D := D) (z := z) (mem_localGroup_of_mem huC) hq hadef
  have haup : a * u ∈ (CFSG.pCore 2 (localGroup D z)).map
      (localGroup D z).subtype := by
    simpa [hS.oddT.inv_eq htri_u.1] using haumemK
  have hcomm_au : Commute a u := by
    by_contra hnc
    have hodd : Odd (orderOf (a * u)) := hS.oddT.odd_of_not_commute haD htri_u.1 hnc
    have h1 : a * u = 1 :=
      CFSG.Timmesfeld.Bridge.OddTransp.eq_one_of_isPGroup_of_odd
        (CFSG.pCore_isPGroup.map (localGroup D z).subtype) haup hodd
    have hau : a = u := by
      have h := congrArg (fun x : G => x * u) h1
      simpa [mul_assoc, hS.oddT.mul_self_eq_one htri_u.1] using h
    exact hqa_u (by rw [hau]; exact halpha_d)
  exact ⟨by simpa [ha_def, hu_def] using haD,
    by simpa [ha_def, hu_def] using hcomm_au⟩

theorem conj_pCore_not_mem_alpha_mem_DalphaStar (hC : HypothesisC D)
    {w v : G} (htri : IsTriangle D hC.d w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (hC.d * v * w) = 2 * n) {z : G} (hzdef : (hC.d * v * w) ^ n = z)
    {q : localGroup D z} (hq : q ∈ CFSG.pCore 2 (localGroup D z))
    (hqa : (q : G) * hC.d * (q : G)⁻¹ ∉ hC.alpha) :
    (q : G) * hC.d * (q : G)⁻¹ ∈ DalphaStar D hC.alpha := by
  obtain ⟨haD, hcomm⟩ :=
    conj_pCore_not_mem_alpha_mem_D_and_commute hC htri hn hord hzdef hq hqa
  exact mem_DalphaStar_of_mem_D_of_not_mem_alpha_of_commute hC hC.d_mem_alpha haD hqa
    (by simpa using hcomm)

theorem exists_conj_triangle_of_DalphaStar (hC : HypothesisC D)
    {w v : G} (htri : IsTriangle D hC.d w v) {n : ℕ}
    (hord : orderOf (hC.d * v * w) = 2 * n) {z : G} (hzdef : (hC.d * v * w) ^ n = z)
    {a : G} (haStar : a ∈ DalphaStar D hC.alpha) (hv : v ∈ DalphaStar D hC.alpha)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * hC.d * k⁻¹ = x) :
    ∃ c t : G, IsTriangle D hC.d c a ∧ orderOf (hC.d * a * c) = 2 * n ∧
      (hC.d * a * c) ^ n = t ∧
      ∀ x ∈ centSet D t, ∃ k ∈ localGroup D t, k * hC.d * k⁻¹ = x := by
  classical
  have hS := hC.setup
  set u : G := hC.d with hu_def
  have htri_u : IsTriangle D u w v := by simpa [hu_def] using htri
  have hord_u : orderOf (u * v * w) = 2 * n := by simpa [hu_def] using hord
  have hzdef_u : (u * v * w) ^ n = z := by simpa [hu_def] using hzdef
  have htrans_u : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x := by
    simpa [hu_def] using htrans
  obtain ⟨h, hhH, hhv⟩ := hC.Halpha_transitive v hv a haStar
  have hh_cent : Commute h u := by
    have hmem : h ∈ Subgroup.centralizer ({u} : Set G) :=
      Halpha_le_centralizer_d hC (by simpa [hu_def] using hhH)
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem
  have hgu : h * u * h⁻¹ = u := by
    rw [hh_cent.eq]
    group
  set c : G := h * w * h⁻¹ with hc_def
  have htri' : IsTriangle D u c a := by
    have h := isTriangle_conj hS.normal htri_u (g := h)
    simpa [hc_def, hgu, hhv] using h
  have hconj : h * (u * v * w) * h⁻¹ = u * a * c := by
    calc h * (u * v * w) * h⁻¹
        = (h * u * h⁻¹) * (h * v * h⁻¹) * (h * w * h⁻¹) := by group
      _ = u * a * c := by rw [hgu, hhv, hc_def]
  have hord' : orderOf (u * a * c) = 2 * n := by
    rw [← hconj, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hord_u]
  set t : G := h * z * h⁻¹ with ht_def
  have htpow : (u * a * c) ^ n = t := by
    rw [← hconj, ← MulAut.conj_apply, ← map_pow, hzdef_u, MulAut.conj_apply, ht_def]
  have htrans_t : ∀ x ∈ centSet D t, ∃ k ∈ localGroup D t, k * u * k⁻¹ = x := by
    have h := transitive_conj_of_conj_eq hS hgu htrans_u
    simpa [ht_def] using h
  exact ⟨c, t, by simpa [hu_def] using htri', by simpa [hu_def] using hord',
    by simpa [hu_def] using htpow, by simpa [hu_def] using htrans_t⟩

section Certificates


theorem exists_commute_of_conj_pCore_not_mem_alpha (hC : HypothesisC D)
    {w v : G} (htri : IsTriangle D hC.d w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (hC.d * v * w) = 2 * n) {z : G} (hzdef : (hC.d * v * w) ^ n = z)
    (hv : v ∈ DalphaStar D hC.alpha)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * hC.d * k⁻¹ = x)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    {q : localGroup D z} (hq : q ∈ CFSG.pCore 2 (localGroup D z))
    (hqa : (q : G) * hC.d * (q : G)⁻¹ ∉ hC.alpha) :
    ∃ r ∈ D, Commute r hC.d ∧ Commute r v ∧ Commute r w := by
  classical
  set a : G := (q : G) * hC.d * (q : G)⁻¹ with ha_def
  have hadef : (q : G) * hC.d * (q : G)⁻¹ = a := ha_def.symm
  have haStar : a ∈ DalphaStar D hC.alpha :=
    conj_pCore_not_mem_alpha_mem_DalphaStar hC htri hn hord hzdef hq hqa
  obtain ⟨c, t, htri', hord', htpow, htrans_t⟩ :=
    exists_conj_triangle_of_DalphaStar hC htri hord hzdef haStar hv htrans
  exact exists_commute_of_thirdKind_conj_pCore hC.setup htri hn hn1 hord hzdef htrans hB hq
    hadef htri' hn hord' htpow htrans_t

end Certificates

end CFSG.OddTranspositions.PartThree
