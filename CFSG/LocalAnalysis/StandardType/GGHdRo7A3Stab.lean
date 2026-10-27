module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic

import CFSG.LocalAnalysis.StandardType.GGHdRo7CLStab
import CFSG.LocalAnalysis.StandardType.GGHdRo7LNC
import CFSG.LocalAnalysis.StandardType.GGSCNoTVCyclic
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.GroupTheory.GL52.SylowTools

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7A3StabAux_row_noncyclic {G : Type} [Group G] [Finite G]
    {p : ℕ} {J X : Subgroup G} (hrow : GGResRowAt ggRowSUCorank3 p J X) :
    ∃ S : Subgroup G, S ≤ X ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  obtain ⟨labJ, labX, -, -, -, hXlab, hr⟩ := hrow
  obtain ⟨hp3, -, -, hXtag, hXn, -, h8, -⟩ := hr
  subst hp3
  exact CFSG.StandardType.HdRo7LNC.hdRo7LNCAux_su_noncyclic hXtag hXn (by omega) hXlab

private lemma hdRo7A3StabAux_sstar
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (h3 : p = 3) (hy : y ∈ Bs)
    (hcen : ∀ e ∈ Bs ⊓ Subgroup.centralizer (K : Set G), e ∈ Subgroup.zpowers y) :
    LargeEvenSStar p B y K := by
  subst h3
  obtain ⟨hConf, -, hIDAll, hNoTV, hNbr, -, -⟩ := hH
  obtain ⟨hThmI, hBstar, hStdSub⟩ := hConf
  have hStdType := hThmI.2.2.2.2.2.2.2
  obtain ⟨-, hE, -, hSC⟩ := hBstar
  obtain ⟨hBmax, hyB, hy1, -, -, -⟩ := hNbr.1
  have hcomp := isComponentOf_of_isNeighborOf hStdType (isNeighborOf_of_ggNbr hStdSub hNbr)
  have hcard : Nat.card (Bs ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤ 3 := by
    have hle : (Bs ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤ Subgroup.zpowers y :=
      hcen
    have hcard' := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at hcard'
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hE.2 y hy)
    have hne1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
    have horder : orderOf y = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne1
    rwa [horder] at hcard'
  have hEC : Bs ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
    fun b hb => normalizer_le_normalizer_centralizer K
      (ggInnerDiagOn_le_normalizer (hIDAll.2 y K hNbr) hb)
  exact ⟨hBmax, hyB, hy1, hcomp.1, fun S hSle hSp =>
    ggSCNoTV_isCyclic (p := 3) (by norm_num) hE hSC hNoTV hEC hcard hSle hSp⟩

private theorem hdRo7A3StabAux_kstab
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {y : G} {K : Subgroup G}
    (hS : LargeEvenSStar p B y K)
    (hnc : ∃ S : Subgroup G, S ≤ K ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hy : y ∈ Bs) {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizer ⊤ Bs)
    (hψy : ψ ⟨y, hy⟩ = ⟨y, hy⟩) :
    ∀ φ ∈ ggAutomizer K Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer K Bs := by
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hψ
  have hgy_eq : g * y * g⁻¹ = y := by
    have h1 : g * (⟨y, hy⟩ : ↥Bs) * g⁻¹ = (⟨y, hy⟩ : ↥Bs) := by
      rw [← hφg (⟨y, hy⟩ : ↥Bs), hψy]
    simpa using h1
  have hgy : g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
    CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem (by
      rw [hgy_eq]
      exact Subgroup.mem_zpowers y)
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_of_sstar' hS hnc hgy
  intro φ hφ
  obtain ⟨l, hl, hlN, hφl⟩ := mem_ggAutomizer_iff.mp hφ
  refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgK l).mp hl
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN)
  · intro b
    rw [MulAut.mul_apply, MulAut.mul_apply, hφg, hφl, inv_apply_of_forall hφg]
    group

theorem a3_lstab_holds : A3LStabLeaf := by
  intro G _ _ p B Bs x L D J y K hH hpFact hrow hx ψ hψ hψx
  exact hdRo7CLStab_normalizes hH (hdRo7A3StabAux_row_noncyclic hrow) hx hψ hψx

theorem a3_kstab_holds : A3KStabLeaf := by
  intro G _ _ p B Bs x L D J y K hH hpFact hrow hy hcen ψ hψ hψy
  have h3 : p = 3 := by
    obtain ⟨labJ, labX, h1, h2, hJlab, hXlab, hr⟩ := hrow
    exact hr.1
  exact hdRo7A3StabAux_kstab (hdRo7A3StabAux_sstar hH h3 hy hcen)
    (hdRo7A3StabAux_row_noncyclic hrow) hy hψ hψy

end CFSG.StandardType.HdRo7A3
