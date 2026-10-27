module

public import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoStatement
public import CFSG.OddTranspositions.HypothesisC

import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralBlocks
import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCore
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.SixNineUnconditional
import CFSG.OddTranspositions.SixFiveInputs
import CFSG.OddTranspositions.BlockTransitive
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.WidthOne
import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem exists_pCore_conj_ne_of_not_le_center {z u : G}
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hQ : ¬ CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z)) :
    ∃ q ∈ CFSG.pCore 2 (localGroup D z), (q : G) * u * (q : G)⁻¹ ≠ u := by
  by_contra hcon
  push Not at hcon
  apply hQ
  intro q hq
  have hcomm : ∀ x ∈ centSet D z, Commute (q : G) x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := htrans x hx
    have hq' : (⟨k, hk⟩ : localGroup D z)⁻¹ * q * ⟨k, hk⟩ ∈ CFSG.pCore 2 (localGroup D z) := by
      simpa using (CFSG.pCore_normal (p := 2) (G := localGroup D z)).conj_mem q hq
        (⟨k, hk⟩ : localGroup D z)⁻¹
    have h1 : (k⁻¹ * (q : G) * k) * u * (k⁻¹ * (q : G) * k)⁻¹ = u := by
      simpa using hcon _ hq'
    rw [commute_iff_eq]
    calc (q : G) * (k * u * k⁻¹)
        = k * ((k⁻¹ * (q : G) * k) * u * (k⁻¹ * (q : G) * k)⁻¹) * k⁻¹ * q := by group
      _ = k * u * k⁻¹ * q := by rw [h1]
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : Commute (q : G) (g : G) :=
    commute_of_mem_closure (S := {(q : G)}) (S' := centSet D z)
      (fun s hs x hx => by rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hcomm x hx)
      (Subgroup.subset_closure rfl) g.2
  exact Subtype.ext hg.eq.symm

theorem commute_conj_pCore (hS : Setup G D) {z u : G} (hu : u ∈ centSet D z)
    {q : localGroup D z} (hq : q ∈ CFSG.pCore 2 (localGroup D z)) :
    Commute ((q : G) * u * (q : G)⁻¹) u := by
  have haD : (q : G) * u * (q : G)⁻¹ ∈ D := hS.normal (q : G) u hu.1
  have hmem : (q : G) * u * (q : G)⁻¹ * u⁻¹ ∈
      (CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype :=
    conj_mul_inv_mem_pCore (mem_localGroup_of_mem hu) hq rfl
  rw [hS.oddT.inv_eq hu.1] at hmem
  exact commute_of_mul_mem_of_isPGroup hS.oddT
    (CFSG.pCore_isPGroup.map (localGroup D z).subtype) haD hu.1 hmem

theorem pairwise_commute_of_conj_pCore_mem_block (hS : Setup G D) {β : Set G}
    (hβ : IsBlock D β) {u w v : G} (hu : u ∈ β) (htri : IsTriangle D u w v) {n : ℕ}
    (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) {z : G}
    (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hQ : ¬ CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hβQ : ∀ q ∈ CFSG.pCore 2 (localGroup D z), (q : G) * u * (q : G)⁻¹ ∈ β)
    (hv : v ∈ DalphaStar D β) (hb : u * v * z ∈ DalphaStar D β) :
    ∀ c ∈ β, ∀ c' ∈ β, Commute c c' := by
  classical
  have hD := hS.oddT
  have hN := hS.normal
  obtain ⟨hzz, -, -, hzv, -, -⟩ := htri.third_kind hD hN hn hord
  obtain ⟨huC, -, -, hbC⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at hzz hzv huC hbC
  have hnorm : ∀ {g x : G}, x ∈ β → g * x * g⁻¹ ∈ β → g ∈ Subgroup.normalizer β := by
    intro g x hx hgx
    by_contra hg
    exact Set.disjoint_left.mp (hβ.disjoint_conj hg) hgx ⟨x, hx, rfl⟩
  have hstar : ∀ {x c : G}, x ∈ DalphaStar D β → c ∈ β → Commute c x := by
    intro x c hx hc
    obtain ⟨γ, hγ, hxγ⟩ := hx
    exact (mem_Dalpha_iff.mp hγ).2.2.2 c hc x hxγ
  obtain ⟨q, hq, hqu⟩ := exists_pCore_conj_ne_of_not_le_center htrans hQ
  set a : G := (q : G) * u * (q : G)⁻¹ with ha_def
  have haD : a ∈ D := hN _ _ htri.1
  have hau : Commute a u := commute_conj_pCore hS huC hq
  have hqN : (q : G) ∈ Subgroup.normalizer β := hnorm hu (hβQ q hq)
  have hqz : Commute (q : G) z := commute_of_mem_localGroup q.2
  set b : G := u * v * z with hb_def
  set v' : G := (q : G) * v * (q : G)⁻¹ with hv'_def
  set b' : G := (q : G) * b * (q : G)⁻¹ with hb'_def
  have hv' : v' ∈ DalphaStar D β := DalphaStar.invariant_normalizer hN hqN v hv
  have hb' : b' ∈ DalphaStar D β := DalphaStar.invariant_normalizer hN hqN b hb
  have hqzq : (q : G) * z * (q : G)⁻¹ = z := by rw [hqz.eq]; group
  have hb'eq : b' = a * v' * z := by
    calc b' = ((q : G) * u * (q : G)⁻¹) * ((q : G) * v * (q : G)⁻¹) *
          ((q : G) * z * (q : G)⁻¹) := by rw [hb'_def, hb_def]; group
      _ = a * v' * z := by rw [hqzq]
  have hzb' : Commute z b' := by
    have h := (Commute.conj_iff (q : G)).mpr hbC.2.symm
    rwa [hqzq] at h
  have hv'2 : v' * v' = 1 := by
    rw [hv'_def]
    calc (q : G) * v * (q : G)⁻¹ * ((q : G) * v * (q : G)⁻¹) = (q : G) * (v * v) * (q : G)⁻¹ := by
          group
      _ = 1 := by rw [hD.mul_self_eq_one htri.2.1]; group
  have hu_eq : u = b * z * v := by
    rw [hb_def]
    calc u = u * v * (z * z) * v := by
          rw [hzz, mul_one, mul_assoc, hD.mul_self_eq_one htri.2.1, mul_one]
      _ = u * v * z * z * v := by group
  have ha_eq : a = b' * z * v' := by
    rw [hb'eq]
    calc a = a * v' * (z * z) * v' := by rw [hzz, mul_one, mul_assoc, hv'2, mul_one]
      _ = a * v' * z * z * v' := by group
  have hprod : u * a = b * v * b' * v' := by
    calc u * a = b * (z * v) * (b' * z) * v' := by rw [hu_eq, ha_eq]; group
      _ = b * (v * z) * (z * b') * v' := by rw [hzv.eq, ← hzb'.eq]
      _ = b * v * (z * z) * b' * v' := by group
      _ = b * v * b' * v' := by rw [hzz, mul_one]
  have hcu : ∀ c ∈ β, Commute c u := by
    intro c hc
    have hcua : Commute c (u * a) := by
      rw [hprod]
      exact (((hstar hb hc).mul_right (hstar hv hc)).mul_right (hstar hb' hc)).mul_right
        (hstar hv' hc)
    exact ((hD.commute_mul_iff htri.1 haD (hβ.subset hc) (Ne.symm hqu) hau.symm).mp hcua).1
  intro c hc c' hc'
  obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj htri.1 (hβ.subset hc))
  have hgN : g ∈ Subgroup.normalizer β := hnorm hu (by rw [hg]; exact hc)
  have hg' : g⁻¹ * c' * g ∈ β := by
    have := (Subgroup.inv_mem _ hgN : g⁻¹ ∈ Subgroup.normalizer β) c'
    simpa using this.mp hc'
  have h := (Commute.conj_iff g).mpr (hcu _ hg')
  rw [hg, show g * (g⁻¹ * c' * g) * g⁻¹ = c' by group] at h
  exact h.symm

theorem block_pairwise_commute_of_uQ_subset (hC : HypothesisC D)
    {w v : G} (htri : IsTriangle D hC.d w v) (hv : v ∈ DalphaStar D hC.alpha)
    {n : ℕ} (hn : Odd n) (hord : orderOf (hC.d * v * w) = 2 * n)
    {z : G} (hzdef : (hC.d * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * hC.d * k⁻¹ = x)
    (hQ : ¬ CFSG.pCore 2 (localGroup D z) ≤ Subgroup.center (localGroup D z))
    (hα : ∀ q ∈ CFSG.pCore 2 (localGroup D z), (q : G) * hC.d * (q : G)⁻¹ ∈ hC.alpha) :
    ∀ c ∈ hC.alpha, ∀ c' ∈ hC.alpha, Commute c c' := by
  classical
  have hS := hC.setup
  have hD := hS.oddT
  have hN := hS.normal
  obtain ⟨-, -, hzu, hzv, -, hbD⟩ := htri.third_kind hD hN hn hord
  obtain ⟨-, hvC, -, -⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at hzu hzv hbD hvC
  have huv : Commute hC.d v := htri.2.2.2.2.1
  have hbu : Commute (hC.d * v * z) hC.d :=
    ((Commute.refl hC.d).mul_left huv.symm).mul_left hzu
  have hbv : Commute (hC.d * v * z) v := (huv.mul_left (Commute.refl v)).mul_left hzv
  have hvα : v ∉ hC.alpha := fun h =>
    Set.disjoint_left.mp (disjoint_alpha_DalphaStar hC.isBlock_alpha) h hv
  by_cases hbα : hC.d * v * z ∈ hC.alpha
  ·
    obtain ⟨k, hk, hkv⟩ := htrans v hvC
    set hC' : HypothesisC D := hC.conj k with hC'_def
    have hC'd : hC'.d = v := hkv
    have hC'α : hC'.alpha = cimg k hC.alpha := HypothesisC.conj_alpha hC k
    have hvβ : v ∈ hC'.alpha := hC'd ▸ hC'.d_mem_alpha
    have hβclass : hC'.alpha ∈ blockClass hC.alpha := by
      rw [hC'α]
      exact mem_blockClass_iff.mpr ⟨k, rfl⟩
    have hnotβ : ∀ x ∈ hC.alpha, x ∉ hC'.alpha := by
      intro x hx hxβ
      have heq := eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβclass
        (mem_blockClass_self hC.alpha) ⟨x, hxβ, hx⟩
      exact hvα (heq ▸ hvβ)
    have huStar : hC.d ∈ DalphaStar D hC'.alpha :=
      mem_DalphaStar_of_mem_D_of_not_mem_alpha_of_commute hC' hvβ hC.hd
        (hnotβ _ hC.d_mem_alpha) huv
    have hbStar : v * hC.d * z ∈ DalphaStar D hC'.alpha := by
      rw [← huv.eq]
      exact mem_DalphaStar_of_mem_D_of_not_mem_alpha_of_commute hC' hvβ hbD (hnotβ _ hbα) hbv
    have htri' : IsTriangle D v w hC.d :=
      ⟨htri.2.1, htri.1, htri.2.2.1, htri.2.2.2.1.symm, huv.symm, htri.2.2.2.2.2.2,
        htri.2.2.2.2.2.1⟩
    have hord' : orderOf (v * hC.d * w) = 2 * n := by rw [← huv.eq]; exact hord
    have hzdef' : (v * hC.d * w) ^ n = z := by rw [← huv.eq]; exact hzdef
    have hβQ : ∀ q ∈ CFSG.pCore 2 (localGroup D z), (q : G) * v * (q : G)⁻¹ ∈ hC'.alpha := by
      intro q hq
      have hq' : (⟨k, hk⟩ : localGroup D z)⁻¹ * q * ⟨k, hk⟩ ∈ CFSG.pCore 2 (localGroup D z) := by
        simpa using (CFSG.pCore_normal (p := 2) (G := localGroup D z)).conj_mem q hq
          (⟨k, hk⟩ : localGroup D z)⁻¹
      have h1 : (k⁻¹ * (q : G) * k) * hC.d * (k⁻¹ * (q : G) * k)⁻¹ ∈ hC.alpha := by
        simpa using hα _ hq'
      rw [hC'α, mem_cimg, ← hkv]
      convert h1 using 1
      group
    have hcomm' := pairwise_commute_of_conj_pCore_mem_block hS hC'.isBlock_alpha hvβ htri' hn
      hord' hzdef' (transitive_pair_of_transitive htrans v hvC) hQ hβQ huStar hbStar
    intro c hc c' hc'
    have hkc : k * c * k⁻¹ ∈ hC'.alpha := by rw [hC'α]; exact ⟨c, hc, rfl⟩
    have hkc' : k * c' * k⁻¹ ∈ hC'.alpha := by rw [hC'α]; exact ⟨c', hc', rfl⟩
    exact (Commute.conj_iff k).mp (hcomm' _ hkc _ hkc')
  ·
    exact pairwise_commute_of_conj_pCore_mem_block hS hC.isBlock_alpha hC.d_mem_alpha htri hn
      hord hzdef htrans hQ hα hv
      (mem_DalphaStar_of_mem_D_of_not_mem_alpha_of_commute hC hC.d_mem_alpha hbD hbα hbu)

theorem not_mem_alpha_of_isTriangle (hC : HypothesisC D)
    (hcomm : ∀ c ∈ hC.alpha, ∀ c' ∈ hC.alpha, Commute c c') {c a : G}
    (htri : IsTriangle D hC.d c a) : c ∉ hC.alpha :=
  fun hc => htri.2.2.2.2.2.1 (hcomm _ hC.d_mem_alpha c hc)

end CFSG.OddTranspositions.PartThree
