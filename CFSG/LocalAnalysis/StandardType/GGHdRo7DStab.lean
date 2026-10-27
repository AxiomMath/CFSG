module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs

import CFSG.LocalAnalysis.StandardType.GGSCNoTVCyclic
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatAct
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8OmRank
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.GroupTheory.GL52.SylowTools
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGResHyp.sstar_K_of_centralizer_axis
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hcen : ∀ e ∈ Bs ⊓ Subgroup.centralizer (K : Set G), e ∈ Subgroup.zpowers y) :
    LargeEvenSStar p B y K := by
  obtain ⟨hConf, -, hIDAll, hNoTV, hNbr, -, -⟩ := hH
  obtain ⟨hThmI, hBstar, hStdSub⟩ := hConf
  have hStdType := hThmI.2.2.2.2.2.2.2
  obtain ⟨-, hE, -, hSC⟩ := hBstar
  obtain ⟨hBmax, hyB, hy1, -, -, -⟩ := hNbr.1
  have hcomp := isComponentOf_of_isNeighborOf hStdType (isNeighborOf_of_ggNbr hStdSub hNbr)
  have hcard : Nat.card (Bs ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤ p := by
    have hle : (Bs ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤ Subgroup.zpowers y :=
      hcen
    have hcard' := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at hcard'
    have hdvd : orderOf y ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hE.2 y hy)
    have hne1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
    have horder : orderOf y = p :=
      ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd).resolve_left hne1
    rwa [horder] at hcard'
  have hEC : Bs ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
    fun b hb => normalizer_le_normalizer_centralizer K
      (ggInnerDiagOn_le_normalizer (hIDAll.2 y K hNbr) hb)
  exact ⟨hBmax, hyB, hy1, hcomp.1, fun S hSle hSp =>
    ggSCNoTV_isCyclic (p := p) hThmI.2.2.2.2.2.1.2.1 hE hSC hNoTV hEC hcard hSle hSp⟩

end CFSG.StandardType

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DStabAux_orth_noncyclic_plus {G : Type} [Group G] [Finite G]
    {X : Subgroup G} {l : ℕ} (hl : 5 ≤ l)
    (hR : LargeEvenRecipeOmegaPlus l (2 ^ 1)
      (fun R' _ _ _ => Nonempty (↥X ⧸ Subgroup.center ↥X ≃* R'))) :
    ∃ S : Subgroup G, S ≤ X ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  obtain ⟨K, hField, hFinite, hKcard, ⟨e⟩⟩ := hR
  have hK : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om.bigElem_plus_two K hK hl
  let ψ : ↥X →* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K l)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine exists_noncyclic_of_noncyclic_quot (F := E) ψ hψ ?_ ?_
  · intro x
    exact ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  · have hexp : ∀ x ∈ E, x ^ 3 = 1 := hE.2
    have hcard : 3 < Nat.card ↥E := by
      have h1 : 3 ^ 4 ≤ Nat.card ↥E := hEcard
      calc 3 < 3 ^ 4 := by norm_num
        _ ≤ Nat.card ↥E := h1
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.not_isCyclic_of_exponent
      Nat.prime_three hexp hcard

private lemma hdRo7DStabAux_orth_noncyclic_minus {G : Type} [Group G] [Finite G]
    {X : Subgroup G} {l : ℕ} (hl : 5 ≤ l)
    (hR : LargeEvenRecipeOmegaMinus (l - 1) (2 ^ 1)
      (fun R' _ _ _ => Nonempty (↥X ⧸ Subgroup.center ↥X ≃* R'))) :
    ∃ S : Subgroup G, S ≤ X ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  obtain ⟨K, hField, hFinite, hKcard, b, c, hirr, ⟨e⟩⟩ := hR
  have hK : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om.bigElem_minus_two K hK hl b c hirr
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus l K b c)) :=
    e.trans (omegaMinusProjEquiv l b c)
  let ψ : ↥X →* CFSG.Open.StatedProj
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus l K b c)) :=
    e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hψ : Function.Surjective ψ := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine exists_noncyclic_of_noncyclic_quot (F := E) ψ hψ ?_ ?_
  · intro x
    exact ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  · have hexp : ∀ x ∈ E, x ^ 3 = 1 := hE.2
    have hcard : 3 < Nat.card ↥E := by
      have h1 : 3 ^ 4 ≤ Nat.card ↥E := hEcard
      calc 3 < 3 ^ 4 := by norm_num
        _ ≤ Nat.card ↥E := h1
    exact CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.not_isCyclic_of_exponent
      Nat.prime_three hexp hcard

private lemma hdRo7DStabAux_orth_noncyclic {G : Type} [Group G] [Finite G]
    {X : Subgroup G} {lab : LargeEvenLabel}
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hn : lab.n = 1) (h5 : 5 ≤ lab.rank)
    (hR : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X)) :
    ∃ S : Subgroup G, S ≤ X ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  rw [GGHasLabel] at hR
  rcases lab with ⟨t, l, n⟩
  simp only at htag hn h5 hR
  subst hn
  have hl3 : l ≠ 3 := by omega
  have hl2 : l ≠ 2 := by omega
  rcases htag with rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hR
    rw [if_neg hl3] at hR
    exact hdRo7DStabAux_orth_noncyclic_plus h5 hR
  · dsimp only [LargeEvenRawDatum] at hR
    rw [if_neg hl2, if_neg hl3] at hR
    exact hdRo7DStabAux_orth_noncyclic_minus h5 hR

private lemma hdRo7DStabAux_row_noncyclic {G : Type} [Group G] [Finite G]
    {p : ℕ} {J X : Subgroup G} (hrow : GGResRowAt ggRowDCorank2 p J X) :
    ∃ S : Subgroup G, S ≤ X ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  obtain ⟨labJ, labX, -, -, -, hXlab, hr⟩ := hrow
  obtain ⟨hp3, -, hXtag, -, hXn, -, h6⟩ := hr
  subst hp3
  exact hdRo7DStabAux_orth_noncyclic hXtag hXn (by omega) hXlab

private lemma hdRo7DStabAux_normalizes
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hx : x ∈ Bs) {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizer ⊤ Bs)
    (hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ φ ∈ ggAutomizer L Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer L Bs := by
  have hS := hH.1.1.2.2.2.2.2.2.1
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hψ
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := by
    refine mem_normalizer_of_sstar' hS hnc ?_
    apply CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem
    have hconj : g * x * g⁻¹ = x := by
      have h1 : g * (⟨x, hx⟩ : ↥Bs) * g⁻¹ = (⟨x, hx⟩ : ↥Bs) := by
        rw [← hφg (⟨x, hx⟩ : ↥Bs), hψx]
      simpa using h1
    rw [hconj]
    exact Subgroup.mem_zpowers x
  intro φ hφ
  obtain ⟨l, hl, hlN, hφl⟩ := mem_ggAutomizer_iff.mp hφ
  refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgL l).mp hl
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN)
  · intro b
    rw [MulAut.mul_apply, MulAut.mul_apply, hφg, hφl, inv_apply_of_forall hφg]
    group

private theorem hdRo7DStabAux_kstab
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

theorem d_lstab_holds : DLStabLeaf := by
  intro G _ _ p B Bs x L D J y K hH hpFact hrow hx ψ hψ hψx
  exact hdRo7DStabAux_normalizes hH (hdRo7DStabAux_row_noncyclic hrow) hx hψ hψx

theorem d_lstab_of_label {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hp3 : p = 3) {lab : LargeEvenLabel} (htag : lab.tag = .D ∨ lab.tag = .twD) (hn : lab.n = 1)
    (h5 : 5 ≤ lab.rank) (hlab : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) (hx : x ∈ Bs)
    {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizer ⊤ Bs) (hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ φ ∈ ggAutomizer L Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer L Bs := by
  subst hp3
  exact hdRo7DStabAux_normalizes hH (hdRo7DStabAux_orth_noncyclic htag hn h5 hlab) hx hψ hψx

theorem d_kstab_holds : DKStabLeaf := by
  intro G _ _ p B Bs x L D J y K hH hpFact hrow hy hcen ψ hψ hψy
  have h3 : p = 3 := by
    obtain ⟨labJ, labX, h1, h2, hJlab, hXlab, hr⟩ := hrow
    exact hr.1
  exact hdRo7DStabAux_kstab (hH.sstar_K_of_centralizer_axis hy hcen)
    (hdRo7DStabAux_row_noncyclic hrow) hy hψ hψy

end CFSG.StandardType.HdRo7D
