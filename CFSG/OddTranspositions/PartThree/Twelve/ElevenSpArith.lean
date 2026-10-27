module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.AUTSL.TraceAS
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
import CFSG.Holt.FoundationsFusion
import CFSG.RankThree.PartOne.AUTSL.TraceASApply
import CFSG.ClassicalGroups.Alternating.RT1SpGeneration
import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelRoot
import CFSG.ClassicalGroups.Orthogonal.PolarPairPlane
import CFSG.ClassicalInvolution.Asc77.AscE189OrthV
import CFSG.ClassicalInvolution.ModelFacts.MF15Sign
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.TwistedConfig
import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
import CFSG.RankThree.PartOne.S11d.PSpCyclic
import CFSG.ClassicalInvolution.RouteD.TWYType
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.ClassicalInvolution.ModelFacts.MF15Sq
import CFSG.ClassicalInvolution.Models.LinearPairs
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.Holt.Basic
import CFSG.Holt.Centralizer
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.GroupTheory.WeirSylow CFSG.Open CFSG.RankThree.Classical
  CFSG.ClassicalGroups.Alternating CFSG.RankThree.PartOne.AUTSL CFSG.RankThree.PartOne.KCSpFull
open CFSG.RankThree.PartOne.CTP (spTransvection_zero spTransvection_smul)
open CFSG.ComponentClassification.UnbalancedCatalog (polar_self_charTwo)

section ArtinSchreier

variable {K : Type} [Field K] [Fintype K] [CharP K 2]

theorem sq_mem_range_artinSchreier_iff (x : K) :
    x ^ 2 ∈ (artinSchreierHom (K := K)).range ↔
      x ∈ (artinSchreierHom (K := K)).range := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := (frobeniusEquiv K 2).surjective y
    rw [frobeniusEquiv_def] at hz
    refine ⟨z, ?_⟩
    rw [artinSchreierHom_apply]
    have hx2 : x ^ 2 = (z * z + z) ^ 2 := by
      rw [← hy, ← hz]
      rw [artinSchreierHom_apply]
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination - (z ^ 3) * h2
    have hx : x = z * z + z := by
      apply (frobeniusEquiv K 2).injective
      rw [frobeniusEquiv_def, frobeniusEquiv_def]
      exact hx2
    exact hx.symm
  · rintro ⟨y, hy⟩
    refine ⟨y * y, ?_⟩
    rw [← hy]
    rw [artinSchreierHom_apply, artinSchreierHom_apply]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination - (y ^ 3) * h2

theorem eq_zero_of_forall_add_div_mem_range (hK : 2 < Fintype.card K) {A B : K}
    (h : ∀ b : K, b ≠ 0 → A + B / b ∈ (artinSchreierHom (K := K)).range) : B = 0 := by
  classical
  by_contra hB
  let R : AddSubgroup K := (artinSchreierHom (K := K)).range
  let : Fintype R := Fintype.ofFinite R
  let : Fintype (R : Set K) := Subtype.fintype _
  let s : Finset K := Finset.univ.filter (fun b => b ≠ 0)
  let t : Finset K := s.image (fun b => A + B / b)
  have hs_card : s.card = Fintype.card K - 1 := by
    simp only [s]
    rw [Finset.filter_ne' (Finset.univ : Finset K) (0 : K),
      Finset.card_erase_of_mem (Finset.mem_univ (0 : K)), Finset.card_univ]
  have hinj : Set.InjOn (fun b => A + B / b) ↑s := by
    intro b₁ hb₁ b₂ hb₂ heq
    simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
    have hdiv : B / b₁ = B / b₂ := add_left_cancel heq
    have hmul : B * b₂ = B * b₁ := (div_eq_div_iff hb₁ hb₂).mp hdiv
    exact (mul_left_cancel₀ hB hmul).symm
  have ht_card : t.card = s.card := Finset.card_image_of_injOn hinj
  have ht_subset : (t : Set K) ⊆ (R : Set K) := by
    intro x hx
    simp only [t, Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact h b hb
  have hcard_mul : Nat.card R * 2 = Fintype.card K := by
    have h := AddSubgroup.card_mul_index R
    have hR : R.index = 2 := by
      dsimp only [R]
      exact artinSchreierHom_range_index
    rw [hR] at h
    simpa [Nat.card_eq_fintype_card] using h
  have hcardR : Nat.card R = Fintype.card K / 2 := by
    rw [← hcard_mul, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  have hle : t.card ≤ Nat.card R := by
    have h := Set.ncard_le_ncard (s := (t : Set K)) (t := (R : Set K)) ht_subset
    rw [Set.ncard_coe_finset] at h
    rw [← Set.fintypeCard_eq_ncard] at h
    simpa [Nat.card_eq_fintype_card] using h
  rw [ht_card, hs_card, hcardR] at hle
  omega

end ArtinSchreier

theorem exists_affine_of_pencil {K : Type} [Field K] (φ : K → K)
    (h : ∀ b c t : K, b ≠ 0 → c ≠ 0 → (1 - t) * b + t * c ≠ 0 →
      φ ((1 - t) * b + t * c) = (1 - t) * φ b + t * φ c) :
    ∃ A B : K, ∀ b, b ≠ 0 → φ b = A * b + B := by
  by_cases hall : ∀ b : K, b ≠ 0 → b = 1
  · refine ⟨0, φ 1, fun b hb => ?_⟩
    rw [hall b hb]
    ring
  · push Not at hall
    obtain ⟨c₀, hc0, hc1⟩ := hall
    let A := (φ c₀ - φ 1) / (c₀ - 1)
    let B := φ 1 - A
    refine ⟨A, B, fun b hb => ?_⟩
    let t := (b - 1) / (c₀ - 1)
    have hc0' : c₀ - 1 ≠ 0 := sub_ne_zero.mpr hc1
    have hcomb : (1 - t) * 1 + t * c₀ = b := by
      simp only [t]
      field_simp
      ring
    have hne : (1 - t) * 1 + t * c₀ ≠ 0 := by
      rw [hcomb]
      exact hb
    have key := h 1 c₀ t one_ne_zero hc0 hne
    rw [hcomb] at key
    rw [key]
    simp only [A, B, t]
    field_simp
    ring

section PlusType

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
private lemma expand {Q : QuadraticForm K V} {w z : V}
    (h : QuadraticMap.polar Q w z = 1) (a b : K) :
    Q (a • w + b • z) = a * a * Q w + a * b + b * b * Q z := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, h]
  simp only [smul_eq_mul]
  ring

omit [Fintype K] in
private lemma plane_alg (Qw Qz t : K) (hQw : Qw ≠ 0) (ht : t * t + t = Qw * Qz) :
    (t / Qw) * (t / Qw) * Qw + t / Qw + Qz = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  field_simp [hQw]
  linear_combination ht + (Qw * Qz) * h2

private lemma plane_arf_fwd {V₂ : Type} [AddCommGroup V₂] [Module K V₂]
    [FiniteDimensional K V₂] {Q₂ : QuadraticForm K V₂}
    (hdim : Module.finrank K V₂ = 2) {w z : V₂}
    (hB : QuadraticMap.polar Q₂ w z = 1) (hplus : IsPlusType Q₂) :
    Q₂ w * Q₂ z ∈ (artinSchreierHom (K := K)).range := by
  classical
  have hspan : Submodule.span K {w, z} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [CFSG.ClassicalInvolution.ModelFacts.MF15.finrank_span_pair_two
      (CFSG.ClassicalGroups.Orthogonal.OmegaSiegel.linearIndependent_pair_of_polar
        (by rw [hB]; exact one_ne_zero)
        (polar_self_charTwo Q₂ z)
        (by rw [QuadraticMap.polar_comm, hB]; exact one_ne_zero)), hdim]
  obtain ⟨x, hx0, hx⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.H81Orth.exists_singular_of_isPlusType hdim hplus
  have hxmem : x ∈ Submodule.span K {w, z} := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hxmem
  rw [expand hB] at hx
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by
      intro ha
      apply hx0
      rw [ha, hb, zero_smul, zero_smul, add_zero]
    have hQw : Q₂ w = 0 := by
      have hx' : a * a * Q₂ w = 0 := by
        rw [hb] at hx
        simpa using hx
      exact (mul_eq_zero.mp hx').resolve_left (mul_ne_zero ha ha)
    rw [hQw, zero_mul]
    exact AddSubgroup.zero_mem _
  · have hb2 : b * b ≠ 0 := mul_ne_zero hb hb
    have hs : (a / b) * (a / b) * Q₂ w + (a / b) + Q₂ z = 0 := by
      have hmul : b * b * ((a / b) * (a / b) * Q₂ w + (a / b) + Q₂ z)
          = a * a * Q₂ w + a * b + b * b * Q₂ z := by
        field_simp
      have h0 : b * b * ((a / b) * (a / b) * Q₂ w + (a / b) + Q₂ z) = 0 := by
        rw [hmul, hx]
      exact (mul_eq_zero.mp h0).resolve_left hb2
    have hQz : Q₂ z = (a / b) * (a / b) * Q₂ w + (a / b) := by
      have h1 : Q₂ z + ((a / b) * (a / b) * Q₂ w + (a / b)) = 0 := by
        linear_combination hs
      exact CharTwo.add_eq_zero.mp h1
    refine ⟨(a / b) * Q₂ w, ?_⟩
    rw [artinSchreierHom_apply]
    rw [hQz]
    ring

private lemma plane_arf_bwd {V₂ : Type} [AddCommGroup V₂] [Module K V₂]
    [FiniteDimensional K V₂] {Q₂ : QuadraticForm K V₂}
    (hdim : Module.finrank K V₂ = 2) {w z : V₂}
    (hB : QuadraticMap.polar Q₂ w z = 1)
    (hmem : Q₂ w * Q₂ z ∈ (artinSchreierHom (K := K)).range) : IsPlusType Q₂ := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h, QuadraticMap.polar_zero_left] at hB
    exact zero_ne_one hB
  obtain ⟨t, ht⟩ := hmem
  by_cases hQw : Q₂ w = 0
  · by_contra hplus
    exact hwne (CFSG.LocalAnalysis.GLTheoremA.H81Orth.eq_zero_of_not_isPlusType hdim hplus hQw)
  · have hroot : t * t + t = Q₂ w * Q₂ z := (artinSchreierHom_apply t).symm.trans ht
    have hvec : (t / Q₂ w) • w + z ≠ 0 := by
      intro hx0
      have h1 : QuadraticMap.polar Q₂ w ((t / Q₂ w) • w + z) = 0 := by
        rw [hx0, QuadraticMap.polar_zero_right]
      rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        polar_self_charTwo Q₂ w, hB] at h1
      simp only [smul_eq_mul, mul_zero, zero_add] at h1
      exact zero_ne_one h1.symm
    have hQvec : Q₂ ((t / Q₂ w) • w + z) = 0 := by
      have hexp := expand (Q := Q₂) hB (t / Q₂ w) 1
      rw [one_smul] at hexp
      rw [hexp]
      simp only [mul_one, one_mul]
      exact plane_alg (Q₂ w) (Q₂ z) t hQw hroot
    by_contra hplus
    exact hvec (CFSG.LocalAnalysis.GLTheoremA.H81Orth.eq_zero_of_not_isPlusType hdim hplus hQvec)

private lemma plane_arf {V₂ : Type} [AddCommGroup V₂] [Module K V₂]
    [FiniteDimensional K V₂] {Q₂ : QuadraticForm K V₂}
    (hdim : Module.finrank K V₂ = 2) {w z : V₂}
    (hB : QuadraticMap.polar Q₂ w z = 1) :
    IsPlusType Q₂ ↔ Q₂ w * Q₂ z ∈ (artinSchreierHom (K := K)).range :=
  ⟨plane_arf_fwd hdim hB, plane_arf_bwd hdim hB⟩

omit [Fintype K] [FiniteDimensional K V] in
private lemma polar_add_sq {Q Q' : QuadraticForm K V} (w : V)
    (hQ' : ∀ x, Q' x = Q x + QuadraticMap.polar Q w x ^ 2) (x y : V) :
    QuadraticMap.polar Q' x y = QuadraticMap.polar Q x y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  show Q' (x + y) - Q' x - Q' y = Q (x + y) - Q x - Q y
  rw [hQ' (x + y), hQ' x, hQ' y]
  rw [QuadraticMap.polar_add_right]
  rw [add_sq]
  linear_combination ((QuadraticMap.polar Q w x) * (QuadraticMap.polar Q w y)) * h2

omit [Fintype K] [FiniteDimensional K V] in
private lemma polarBilin_add_sq {Q Q' : QuadraticForm K V} (w : V)
    (hQ' : ∀ x, Q' x = Q x + QuadraticMap.polar Q w x ^ 2) :
    QuadraticMap.polarBilin Q' = QuadraticMap.polarBilin Q := by
  ext x y
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
  exact polar_add_sq w hQ' x y

omit [Fintype K] in
private lemma exists_plane_data {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {w : V} (hw : w ≠ 0) :
    ∃ (z : V) (P : Submodule K V), QuadraticMap.polar Q w z = 1 ∧ w ∈ P ∧ z ∈ P ∧
      Module.finrank K P = 2 ∧
      CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q P ∧
      CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
        (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) ∧
      (∀ x ∈ P, ∀ y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P,
        QuadraticMap.polar Q x y = 0) ∧
      IsCompl P (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) := by
  classical
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, QuadraticMap.polar Q w z₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hQ h)
  set z : V := (QuadraticMap.polar Q w z₀)⁻¹ • z₀ with hz_def
  have hB : QuadraticMap.polar Q w z = 1 := by
    rw [hz_def, QuadraticMap.polar_smul_right]
    simpa [smul_eq_mul] using inv_mul_cancel₀ hz₀
  set P : Submodule K V := Submodule.span K {w, z} with hP
  have hwP : w ∈ P := by rw [hP]; exact Submodule.subset_span (by simp)
  have hzP : z ∈ P := by rw [hP]; exact Submodule.subset_span (by simp)
  have hPdim : Module.finrank K P = 2 := by
    rw [hP]
    exact CFSG.ClassicalInvolution.ModelFacts.MF15.finrank_span_pair_two
      (CFSG.ClassicalGroups.Orthogonal.OmegaSiegel.linearIndependent_pair_of_polar
        (by rw [hB]; exact one_ne_zero)
        (polar_self_charTwo Q z)
        (by rw [QuadraticMap.polar_comm, hB]; exact one_ne_zero))
  have hPnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q P := by
    rw [hP]
    exact CFSG.ClassicalGroups.Orthogonal.polarNondegOn_span_pair_of_polar_eq_one hB
  have hcompl : IsCompl P (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isCompl_orthPerp
      (CFSG.ClassicalGroups.Orthogonal.nondegenerate_polarBilin_restrict hPnd)
  have horth : ∀ x ∈ P, ∀ y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P,
      QuadraticMap.polar Q x y = 0 := by
    intro x hx y hy
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) x hx
    simpa [QuadraticMap.polarBilin_apply_apply] using h
  have hPorthND : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) :=
    CFSG.ClassicalInvolution.Asc77.polarNondegOn_of_isCompl hQ hcompl.symm
      (fun x hx y hy => by
        rw [QuadraticMap.polar_comm]
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) y hy
        simpa [QuadraticMap.polarBilin_apply_apply] using h)
  exact ⟨z, P, hB, hwP, hzP, hPdim, hPnd, hPorthND, horth, hcompl⟩

private lemma decomp_Q {Q : QuadraticForm K V} {w z : V} {P : Submodule K V} {m : ℕ}
    (hB : QuadraticMap.polar Q w z = 1) (hwP : w ∈ P) (hzP : z ∈ P)
    (hPdim : Module.finrank K P = 2)
    (hPnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q P)
    (hPorthND : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P))
    (horth : ∀ x ∈ P, ∀ y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P,
      QuadraticMap.polar Q x y = 0)
    (hcompl : IsCompl P (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P))
    (hm : Module.finrank K V = 2 * m) (hm2 : 2 ≤ m) :
    IsPlusType Q ↔ (Q w * Q z ∈ (artinSchreierHom (K := K)).range ↔
      IsPlusType (Q.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P))) := by
  have hPorthdim : Module.finrank K
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) = 2 * (m - 1) := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hm] at h
    have hm1 : 1 ≤ m := le_trans (by norm_num) hm2
    omega
  have hdec : IsPlusType Q ↔ (IsPlusType (Q.restrict P) ↔
      IsPlusType (Q.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P))) :=
    CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl hcompl horth hPnd hPorthND
      (a := 1) (b := m - 1) (by norm_num) (by omega) (by simpa using hPdim) hPorthdim
  have hBp : QuadraticMap.polar (Q.restrict P) ⟨w, hwP⟩ ⟨z, hzP⟩ = 1 := by
    rw [CFSG.ClassicalGroups.Orthogonal.polar_restrict]
    exact hB
  have hplane : IsPlusType (Q.restrict P) ↔
      Q w * Q z ∈ (artinSchreierHom (K := K)).range := by
    have h := plane_arf (Q₂ := Q.restrict P) hPdim hBp
    simpa using h
  rw [hdec, hplane]

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
private lemma polarNondegOn_transfer {Q Q' : QuadraticForm K V} {P : Submodule K V}
    (hpolar : ∀ x y, QuadraticMap.polar Q' x y = QuadraticMap.polar Q x y)
    (hpol : QuadraticMap.polarBilin Q' = QuadraticMap.polarBilin Q)
    (hPnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q P)
    (hPorthND : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P))
    (horth : ∀ x ∈ P, ∀ y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P,
      QuadraticMap.polar Q x y = 0)
    (hcompl : IsCompl P (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P)) :
    CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q' P ∧
      CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q'
        (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q') P) ∧
      (∀ x ∈ P, ∀ y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q') P,
        QuadraticMap.polar Q' x y = 0) ∧
      IsCompl P (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q') P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hx0
    apply hPnd x hx
    intro y hy
    rw [← hpolar x y]
    exact hx0 y hy
  · rw [hpol]
    intro x hx hx0
    apply hPorthND x hx
    intro y hy
    rw [← hpolar x y]
    exact hx0 y hy
  · intro x hx y hy
    rw [hpol] at hy
    rw [hpolar]
    exact horth x hx y hy
  · rw [hpol]
    exact hcompl

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
private lemma restrict_orthogonal_eq {Q Q' : QuadraticForm K V} {w : V} {P : Submodule K V}
    (hQ' : ∀ x, Q' x = Q x + QuadraticMap.polar Q w x ^ 2) (hwP : w ∈ P) :
    Q'.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) =
      Q.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) := by
  ext x
  rw [QuadraticMap.restrict_apply, QuadraticMap.restrict_apply, hQ' x.val]
  have hx : QuadraticMap.polar Q w x.val = 0 := by
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp x.2) w hwP
    simpa [QuadraticMap.polarBilin_apply_apply] using h
  rw [hx]
  simp

private lemma restrict_plane_isPlusType_iff {Q Q' : QuadraticForm K V} {w z : V}
    {P : Submodule K V} (hQ' : ∀ x, Q' x = Q x + QuadraticMap.polar Q w x ^ 2)
    (hB : QuadraticMap.polar Q w z = 1) (hwP : w ∈ P) (hzP : z ∈ P)
    (hPdim : Module.finrank K P = 2) :
    IsPlusType (Q'.restrict P) ↔
      Q w * (Q z + 1) ∈ (artinSchreierHom (K := K)).range := by
  have hself : ∀ x : V, QuadraticMap.polar Q x x = 0 :=
    fun x => polar_self_charTwo Q x
  have hpolar : ∀ x y, QuadraticMap.polar Q' x y = QuadraticMap.polar Q x y :=
    polar_add_sq w hQ'
  have hBp : QuadraticMap.polar (Q'.restrict P) ⟨w, hwP⟩ ⟨z, hzP⟩ = 1 := by
    rw [CFSG.ClassicalGroups.Orthogonal.polar_restrict, hpolar]
    exact hB
  have h := plane_arf (Q₂ := Q'.restrict P) hPdim hBp
  have hQ'w : Q' w = Q w := by rw [hQ' w, hself w]; simp
  have hQ'z : Q' z = Q z + 1 := by rw [hQ' z, hB]; norm_num
  simp only [QuadraticMap.restrict_apply, hQ'w, hQ'z] at h
  exact h

private lemma decomp_Q' {Q Q' : QuadraticForm K V} {w z : V} {P : Submodule K V} {m : ℕ}
    (hQ' : ∀ x, Q' x = Q x + QuadraticMap.polar Q w x ^ 2)
    (hB : QuadraticMap.polar Q w z = 1) (hwP : w ∈ P) (hzP : z ∈ P)
    (hPdim : Module.finrank K P = 2)
    (hPnd : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q P)
    (hPorthND : CFSG.ClassicalGroups.Orthogonal.PolarNondegOn Q
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P))
    (horth : ∀ x ∈ P, ∀ y ∈ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P,
      QuadraticMap.polar Q x y = 0)
    (hcompl : IsCompl P (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P))
    (hm : Module.finrank K V = 2 * m) (hm2 : 2 ≤ m) :
    IsPlusType Q' ↔ ((Q w * Q z ∈ (artinSchreierHom (K := K)).range ↔
      Q w ∈ (artinSchreierHom (K := K)).range) ↔
      IsPlusType (Q.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P))) := by
  have hpolar : ∀ x y, QuadraticMap.polar Q' x y = QuadraticMap.polar Q x y :=
    polar_add_sq w hQ'
  have hpol : QuadraticMap.polarBilin Q' = QuadraticMap.polarBilin Q :=
    polarBilin_add_sq w hQ'
  have hPorthdim : Module.finrank K
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) P) = 2 * (m - 1) := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hm] at h
    have hm1 : 1 ≤ m := le_trans (by norm_num) hm2
    omega
  obtain ⟨hPnd', hPorthND', horth', hcompl'⟩ :=
    polarNondegOn_transfer hpolar hpol hPnd hPorthND horth hcompl
  have hPorthdim' : Module.finrank K
      (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q') P) = 2 * (m - 1) := by
    rw [hpol]
    exact hPorthdim
  have hdec : IsPlusType Q' ↔ (IsPlusType (Q'.restrict P) ↔
      IsPlusType (Q'.restrict
        (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q') P))) :=
    CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_iff_of_isCompl hcompl' horth' hPnd' hPorthND'
      (a := 1) (b := m - 1) (by norm_num) (by omega) (by simpa using hPdim) hPorthdim'
  rw [hpol] at hdec
  have hQ'Porth := restrict_orthogonal_eq hQ' hwP
  have hsum : Q w * (Q z + 1) = Q w * Q z + Q w := by ring
  rw [hdec, hQ'Porth, restrict_plane_isPlusType_iff hQ' hB hwP hzP hPdim, hsum,
    AddSubgroup.add_mem_iff_of_index_two (artinSchreierHom_range_index (K := K))]

theorem isPlusType_add_sq_polar_iff
    {Q Q' : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (w : V)
    (hQ' : ∀ x, Q' x = Q x + QuadraticMap.polar Q w x ^ 2) :
    IsPlusType Q' ↔ (IsPlusType Q ↔ Q w ∈ (artinSchreierHom (K := K)).range) := by
  classical
  have hself : ∀ x : V, QuadraticMap.polar Q x x = 0 :=
    fun x => polar_self_charTwo Q x
  by_cases hw : w = 0
  · subst hw
    have hQ'eq : Q' = Q := by
      ext x
      rw [hQ' x, QuadraticMap.polar_zero_left]
      simp
    have h0 : Q (0:V) ∈ (artinSchreierHom (K := K)).range := by
      rw [QuadraticMap.map_zero]
      exact AddSubgroup.zero_mem _
    rw [hQ'eq]
    tauto
  · obtain ⟨z, P, hB, hwP, hzP, hPdim, hPnd, hPorthND, horth, hcompl⟩ :=
      exists_plane_data hQ hw
    have hdimV : Even (Module.finrank K V) := by
      refine LinearMap.BilinForm.IsAlt.even_finrank ?_ hQ
      intro x
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hself x
    obtain ⟨m, hm⟩ := hdimV
    have hm2 : Module.finrank K V = 2 * m := by omega
    by_cases hdim2 : Module.finrank K V = 2
    · have hplane : IsPlusType Q ↔
          Q w * Q z ∈ (artinSchreierHom (K := K)).range :=
        plane_arf hdim2 hB
      have hB' : QuadraticMap.polar Q' w z = 1 := by rw [polar_add_sq w hQ']; exact hB
      have hplane' : IsPlusType Q' ↔
          Q w * (Q z + 1) ∈ (artinSchreierHom (K := K)).range := by
        have h := plane_arf (Q₂ := Q') hdim2 hB'
        have hQ'w : Q' w = Q w := by rw [hQ' w, hself w]; simp
        have hQ'z : Q' z = Q z + 1 := by rw [hQ' z, hB]; norm_num
        rw [hQ'w, hQ'z] at h
        exact h
      have hsum : Q w * (Q z + 1) = Q w * Q z + Q w := by ring
      rw [hplane', hsum,
        AddSubgroup.add_mem_iff_of_index_two (artinSchreierHom_range_index (K := K)), hplane]
    · have hmge : 2 ≤ m := by
        have hPle : Module.finrank K P ≤ Module.finrank K V := Submodule.finrank_le P
        omega
      have hdecQ := decomp_Q hB hwP hzP hPdim hPnd hPorthND horth hcompl hm2 hmge
      have hdecQ' := decomp_Q' hQ' hB hwP hzP hPdim hPnd hPorthND horth hcompl hm2 hmge
      rw [hdecQ', hdecQ]
      by_cases hA : Q w * Q z ∈ (artinSchreierHom (K := K)).range <;>
        by_cases hb : Q w ∈ (artinSchreierHom (K := K)).range <;> simp [hA, hb]

end PlusType

section Transvections

variable {k : ℕ} {F : Type} [Field F] [CharP F 2]

private lemma mul_spForm_eq_of_spEnd_apply_eq {g : ↥(StatedSp k F)} {y : Fin k ⊕ Fin k → F}
    {φ : (Fin k ⊕ Fin k → F) → F} (hφ : ∀ x, spEnd g x = x + φ x • y) (a b : Fin k ⊕ Fin k → F) :
    φ a * spForm k F b y = φ b * spForm k F a y := by
  have hiso : ∀ a b, spForm k F (spEnd g a) (spEnd g b) = spForm k F a b := by
    intro a b
    have h := CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup.mp (spLin_mem g) a b
    change spForm k F (spEnd g a) (spEnd g b) = spForm k F a b at h
    exact h
  have h := hiso a b
  rw [hφ a, hφ b] at h
  have hexp : spForm k F (a + φ a • y) (b + φ b • y) =
      spForm k F a b + φ b * spForm k F a y + φ a * spForm k F y b := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      spForm_isAlt.self_eq_zero, mul_zero, add_zero]
    ring
  rw [hexp] at h
  have h3 : φ b * spForm k F a y + φ a * spForm k F y b = 0 := by
    linear_combination h
  have h4 : spForm k F y b = - spForm k F b y := (spForm_isAlt.neg_eq b y).symm
  rw [h4] at h3
  rw [CharTwo.neg_eq] at h3
  exact (CharTwo.add_eq_zero.mp h3).symm

omit [CharP F 2] in
private lemma exists_forall_eq_mul_spForm_of_mul_spForm_eq {y : Fin k ⊕ Fin k → F}
    {φ : (Fin k ⊕ Fin k → F) → F}
    (hkey : ∀ a b, φ a * spForm k F b y = φ b * spForm k F a y) (hy : y ≠ 0) :
    ∃ c : F, ∀ x, φ x = c * spForm k F x y := by
  obtain ⟨x', hx'⟩ : ∃ x' : Fin k ⊕ Fin k → F, spForm k F x' y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy (spForm_nondegenerate.2 y hcon)
  let c := φ x' / spForm k F x' y
  have hc : φ x' = c * spForm k F x' y := by
    simp only [c]
    field_simp
  refine ⟨c, fun x => ?_⟩
  have h := hkey x x'
  rw [hc] at h
  have h' : φ x * spForm k F x' y = (c * spForm k F x y) * spForm k F x' y := by
    rw [h]
    ring
  exact mul_right_cancel₀ hx' h'

theorem exists_eq_spTransvection_of_sub_mem_span (g : ↥(StatedSp k F))
    {y : Fin k ⊕ Fin k → F} (h : ∀ x, spEnd g x - x ∈ Submodule.span F {y}) :
    ∃ c : F, g = spTransvection y c := by
  classical
  have hspEnd_inj : Function.Injective
      (spEnd : ↥(StatedSp k F) → Module.End F (Fin k ⊕ Fin k → F)) :=
    CFSG.RankThree.PartOne.spEnd_injective
  have hzero : spTransvection (0 : Fin k ⊕ Fin k → F) (0 : F) = 1 := by
    apply hspEnd_inj
    refine LinearMap.ext fun x => ?_
    rw [spEnd_spTransvection, spEnd_one]
    simp
  by_cases hy : y = 0
  · subst y
    have h1 : g = 1 := by
      apply hspEnd_inj
      refine LinearMap.ext fun x => ?_
      have hx := h x
      rw [Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hx
      rw [sub_eq_zero] at hx
      rw [hx, spEnd_one, Module.End.one_apply]
    exact ⟨0, by rw [h1, hzero]⟩
  · have hex : ∀ x, ∃ c : F, spEnd g x - x = c • y := by
      intro x
      have hx := h x
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, hc⟩ := hx
      exact ⟨c, hc.symm⟩
    choose φ hφ using hex
    have hφeval : ∀ x, spEnd g x = x + φ x • y := by
      intro x
      have h := hφ x
      rw [sub_eq_iff_eq_add] at h
      simpa [add_comm] using h
    have hkey := mul_spForm_eq_of_spEnd_apply_eq hφeval
    obtain ⟨c, hc⟩ := exists_forall_eq_mul_spForm_of_mul_spForm_eq hkey hy
    refine ⟨c, ?_⟩
    apply hspEnd_inj
    refine LinearMap.ext fun x => ?_
    rw [spEnd_spTransvection, hφeval x, hc x]

private lemma exists_unit_spTransvection_of_pair [Fintype F] {y d : Fin k ⊕ Fin k → F} (c : F)
    (hd : spForm k F y d = 0) :
    ∃ w : Fin k ⊕ Fin k → F, spForm k F y w = 0 ∧
      (symplecticTransvection (spForm k F) spForm_isAlt d c : Module.End F _) =
        spEnd (spTransvection w 1) := by
  by_cases hc : c = 0
  · subst hc
    refine ⟨0, by simp, ?_⟩
    rw [spTransvection_zero, spEnd_one]
    ext v
    simp [symplecticTransvection_apply]
  · obtain ⟨e, he⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
    refine ⟨e • d, ?_, ?_⟩
    · rw [map_smul, hd, smul_eq_mul, mul_zero]
    · have hT : spTransvection (e • d) 1 = spTransvection d c := by
        rw [spTransvection_smul]
        rw [← he]
        ring_nf
      rw [← spLin_spTransvection d c, ← hT]

private lemma exists_spTransvection_mul_apply_eq_of_two [Fintype F] {y : Fin k ⊕ Fin k → F}
    {p₁ p₂ : (Fin k ⊕ Fin k → F) × F} {x x' : Fin k ⊕ Fin k → F} {lam : F}
    (hlam : lam ≠ 0) (horth₁ : spForm k F y p₁.1 = 0) (horth₂ : spForm k F y p₂.1 = 0)
    (hmap : ((List.map (fun p => symplecticTransvection (spForm k F) spForm_isAlt p.1 p.2)
        [p₁, p₂]).prod : (Fin k ⊕ Fin k → F) →ₗ[F] (Fin k ⊕ Fin k → F))
      (lam⁻¹ • x) = lam⁻¹ • x') :
    ∃ w₁ w₂, spForm k F y w₁ = 0 ∧ spForm k F y w₂ = 0 ∧
      spEnd (spTransvection w₂ 1 * spTransvection w₁ 1) x = x' := by
  obtain ⟨d₁, c₁⟩ := p₁
  obtain ⟨d₂, c₂⟩ := p₂
  obtain ⟨w₂, hw₂, hfac₂⟩ := exists_unit_spTransvection_of_pair (y := y) c₁ horth₁
  obtain ⟨w₁, hw₁, hfac₁⟩ := exists_unit_spTransvection_of_pair (y := y) c₂ horth₂
  refine ⟨w₁, w₂, hw₁, hw₂, ?_⟩
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hmap
  rw [Units.val_mul, Module.End.mul_apply, hfac₂, hfac₁,
    ← Module.End.mul_apply, ← spEnd_mul, map_smul] at hmap
  have h := congrArg (fun v => lam • v) hmap
  simpa [smul_smul, hlam] using h

theorem exists_spTransvection_mul_apply_eq [Fintype F] {y x x' : Fin k ⊕ Fin k → F}
    (h0 : spForm k F y x ≠ 0) (hxx' : spForm k F y x = spForm k F y x') :
    ∃ w₁ w₂, spForm k F y w₁ = 0 ∧ spForm k F y w₂ = 0 ∧
      spEnd (spTransvection w₂ 1 * spTransvection w₁ 1) x = x' := by
  let lam : F := spForm k F y x
  have hlam : lam ≠ 0 := h0
  have hx1 : spForm k F y (lam⁻¹ • x) = 1 := by
    rw [map_smul]
    show lam⁻¹ * lam = 1
    exact inv_mul_cancel₀ hlam
  have hx'1 : spForm k F y (lam⁻¹ • x') = 1 := by
    rw [map_smul, ← hxx']
    show lam⁻¹ * lam = 1
    exact inv_mul_cancel₀ hlam
  obtain ⟨l, hlen, horth, hfix, hmap⟩ :=
    CFSG.ClassicalGroups.Alternating.alternating_fixed_vector_pair_adjustment (B := spForm k F)
      spForm_isAlt hx1 hx'1
  have hlen2 : l.length = 0 ∨ l.length = 1 ∨ l.length = 2 := by omega
  rcases hlen2 with h0l | h1l | h2l
  · have hl : l = [] := List.length_eq_zero_iff.mp h0l
    subst hl
    simp only [List.map_nil, List.prod_nil] at hmap
    have hxeq : x = x' := by
      have h := congrArg (fun v => lam • v) hmap
      simpa [smul_smul, hlam] using h
    refine ⟨0, 0, by simp, by simp, ?_⟩
    rw [spTransvection_zero, one_mul, spEnd_one]
    exact hxeq
  · obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp h1l
    obtain ⟨d, c⟩ := p
    have hd : spForm k F y d = 0 := horth (d, c) (by simp)
    obtain ⟨w, hw, hfac⟩ := exists_unit_spTransvection_of_pair (y := y) c hd
    refine ⟨w, 0, hw, by simp, ?_⟩
    rw [spTransvection_zero, one_mul]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hmap
    rw [hfac, map_smul] at hmap
    have h := congrArg (fun v => lam • v) hmap
    simpa [smul_smul, hlam] using h
  · obtain ⟨p₁, p₂, rfl⟩ := List.length_eq_two.mp h2l
    exact exists_spTransvection_mul_apply_eq_of_two hlam
      (horth p₁ (by simp)) (horth p₂ (by simp)) hmap

private lemma Tsp_subset_map_closure_of_spLinG [Finite F]
    (spLinG : ↥(StatedSp k F) →* Gsp (spForm k F))
    (hspLinG : ∀ h : ↥(StatedSp k F),
      (spLinG h : LinearMap.GeneralLinearGroup F (Fin k ⊕ Fin k → F)) = spLin k F h)
    (a : Fin k ⊕ Fin k → F) :
    {t : Gsp (spForm k F) | ∃ (x : Fin k ⊕ Fin k → F) (c : F),
        spForm k F a x = 0 ∧ t = Tsp spForm_isAlt x c} ⊆
      (Subgroup.closure ((fun b => spTransvection b 1) ''
        {b | b ≠ 0 ∧ spForm k F a b = 0})).map spLinG := by
  rintro t ⟨x, c, hx, rfl⟩
  by_cases hx0 : x = 0
  · have h1 : Tsp spForm_isAlt x c = 1 :=
      (Tsp_eq_one_iff spForm_isAlt spForm_nondegenerate x c).mpr (Or.inl hx0)
    rw [h1, ← map_one spLinG]
    exact Subgroup.mem_map_of_mem spLinG (Subgroup.one_mem (Subgroup.closure _))
  · by_cases hc0 : c = 0
    · have h1 : Tsp spForm_isAlt x c = 1 :=
        (Tsp_eq_one_iff spForm_isAlt spForm_nondegenerate x c).mpr (Or.inr hc0)
      rw [h1, ← map_one spLinG]
      exact Subgroup.mem_map_of_mem spLinG (Subgroup.one_mem (Subgroup.closure _))
    · obtain ⟨e, he⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
      have he0 : e ≠ 0 := by
        intro h
        rw [h, mul_zero] at he
        exact hc0 he
      have hx' : e • x ≠ 0 := smul_ne_zero he0 hx0
      have horth' : spForm k F a (e • x) = 0 := by
        rw [map_smul, hx, smul_eq_mul, mul_zero]
      have h_eq : spLinG (spTransvection (e • x) 1) = Tsp spForm_isAlt x c := by
        apply Subtype.ext
        change (spLinG (spTransvection (e • x) 1) :
          LinearMap.GeneralLinearGroup F _) =
          symplecticTransvection (spForm k F) spForm_isAlt x c
        rw [hspLinG]
        have hT : spTransvection (e • x) 1 = spTransvection x c := by
          rw [spTransvection_smul]
          rw [mul_one, ← he]
        rw [spLin_spTransvection]
        rw [← spLin_spTransvection (e • x) 1, hT, spLin_spTransvection]
      rw [← h_eq]
      exact Subgroup.mem_map_of_mem spLinG
        (Subgroup.subset_closure ⟨e • x, ⟨hx', horth'⟩, rfl⟩)

theorem mem_closure_spTransvection_of_spEnd_apply_eq [Finite F] {a : Fin k ⊕ Fin k → F}
    {g : ↥(StatedSp k F)} (hg : spEnd g a = a) :
    g ∈ Subgroup.closure
      ((fun b => spTransvection b 1) '' {b | b ≠ 0 ∧ spForm k F a b = 0}) := by
  let B : LinearMap.BilinForm F (Fin k ⊕ Fin k → F) := spForm k F
  let T : Set (StatedSp k F) :=
    (fun b => spTransvection b 1) '' {b | b ≠ 0 ∧ B a b = 0}
  have hle : (spLin k F).range ≤ CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B := by
    intro x hx
    obtain ⟨h, rfl⟩ := hx
    rw [CFSG.RankThree.PartOne.KCSpIsotypic.bilinIsometryGroup_eq_sesqUnitaryGroup]
    exact spLin_mem h
  let spLinG : ↥(StatedSp k F) →* Gsp B :=
    { toFun := fun h => ⟨spLin k F h, hle ⟨h, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        change (spLin k F 1 : LinearMap.GeneralLinearGroup F _) = 1
        rw [map_one]
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (spLin k F (x * y) : LinearMap.GeneralLinearGroup F _) =
          spLin k F x * spLin k F y
        rw [map_mul] }
  have hspLinG_inj : Function.Injective spLinG := by
    intro x y h
    apply spLin_injective
    exact congrArg Subtype.val h
  let g' : Gsp B := spLinG g
  have hg'app : g'.app a = a := by
    change spEnd g a = a
    exact hg
  have hgen : g' ∈ Subgroup.closure
      {t : Gsp B | ∃ (x : Fin k ⊕ Fin k → F) (c : F), B a x = 0 ∧
        t = Tsp spForm_isAlt x c} :=
    CFSG.ClassicalGroups.Alternating.mem_closure_Tsp_of_app_eq (BN := B) spForm_isAlt
      spForm_nondegenerate (g := g') hg'app
  have hsub : {t : Gsp B | ∃ (x : Fin k ⊕ Fin k → F) (c : F), B a x = 0 ∧
      t = Tsp spForm_isAlt x c} ⊆ (Subgroup.closure T).map spLinG :=
    Tsp_subset_map_closure_of_spLinG spLinG (fun h => rfl) a
  have hmem : g' ∈ (Subgroup.closure T).map spLinG :=
    (Subgroup.closure_le (K := (Subgroup.closure T).map spLinG)).mpr hsub hgen
  obtain ⟨h, hh, hhval⟩ := hmem
  have h_eq : spLinG h = spLinG g := by simpa [g'] using hhval
  have : h = g := hspLinG_inj h_eq
  rwa [this] at hh

end Transvections

section Sign

variable {H A : Type} [Group H] [Group A]

private lemma eq_one_of_prod_eq_one (ρ : H →* A) (χ : H →* Multiplicative (ZMod 2)) {z : H}
    (hker : ρ.ker = Subgroup.zpowers z) (hz2 : z ^ 2 = 1)
    (hz : χ z = Multiplicative.ofAdd 1) {h : H} (hh : (ρ.prod χ) h = 1) : h = 1 := by
  have hρh : ρ h = 1 := by
    have := congrArg Prod.fst hh
    simpa using this
  have hχh : χ h = 1 := by
    have := congrArg Prod.snd hh
    simpa using this
  have hmem : h ∈ ρ.ker := MonoidHom.mem_ker.mpr hρh
  rw [hker] at hmem
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h2dvd : (2 : ℤ) ∣ n := by
    have horder : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 := by
      apply orderOf_eq_prime
      · decide
      · decide
    have h1 : χ (z ^ n) = 1 := by rw [hn, hχh]
    have h2 : (χ z) ^ n = 1 := by
      rw [← h1]
      exact (map_zpow χ z n).symm
    have h3 : (Multiplicative.ofAdd (1 : ZMod 2)) ^ n = 1 := by
      rw [← hz]
      exact h2
    have hdiv : (orderOf (Multiplicative.ofAdd (1 : ZMod 2)) : ℤ) ∣ n :=
      (orderOf_dvd_iff_zpow_eq_one).mpr h3
    rwa [horder] at hdiv
  have hord : (orderOf z : ℤ) ∣ (2 : ℤ) :=
    Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hz2)
  have hzn : z ^ n = 1 := orderOf_dvd_iff_zpow_eq_one.mp (dvd_trans hord h2dvd)
  rw [← hn, hzn]

theorem bijective_prod_of_ker_eq_zpowers (ρ : H →* A) (χ : H →* Multiplicative (ZMod 2))
    (hρ : Function.Surjective ρ) {z : H} (hker : ρ.ker = Subgroup.zpowers z) (hz2 : z ^ 2 = 1)
    (hz : χ z = Multiplicative.ofAdd 1) : Function.Bijective (ρ.prod χ) := by
  have hinj_one : ∀ h : H, (ρ.prod χ) h = 1 → h = 1 :=
    fun h hh => eq_one_of_prod_eq_one ρ χ hker hz2 hz hh
  constructor
  · intro h h' hh
    have h1 : h⁻¹ * h' = 1 := by
      apply hinj_one
      rw [map_mul, map_inv, hh]
      exact inv_mul_cancel _
    have h2 : h' = h := by
      calc h' = h * (h⁻¹ * h') := by rw [mul_inv_cancel_left]
        _ = h * 1 := by rw [h1]
        _ = h := by rw [mul_one]
    exact h2.symm
  · rintro ⟨a, ε⟩
    obtain ⟨h, hh⟩ := hρ a
    by_cases hχε : χ h = ε
    · exact ⟨h, by simp [hh, hχε]⟩
    · have htwo : ∀ u : Multiplicative (ZMod 2), u = 1 ∨ u = Multiplicative.ofAdd 1 := by
        decide
      have hρz : ρ z = 1 := by
        have hzmem : z ∈ ρ.ker := by
          rw [hker]
          exact Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]⟩
        exact MonoidHom.mem_ker.mp hzmem
      have hcontra : χ h * Multiplicative.ofAdd 1 = ε := by
        rcases htwo ε with hε | hε
        · rw [hε]
          rcases htwo (χ h) with hχh | hχh
          · rw [hχh, hε] at hχε
            exact absurd rfl hχε
          · rw [hχh]
            decide
        · rw [hε]
          rcases htwo (χ h) with hχh | hχh
          · rw [hχh]
            decide
          · rw [hχh, hε] at hχε
            exact absurd rfl hχε
      refine ⟨h * z, ?_⟩
      change (ρ (h * z), χ (h * z)) = (a, ε)
      rw [map_mul, map_mul, hh, hρz, hz, hcontra, mul_one]

private lemma mul_mem_commutator_or_mem_commutator_of_closure_eq_top {S : Set H}
    (hS : Subgroup.closure S = ⊤) {z : H} (hz2 : z ^ 2 = 1)
    (hSz : ∀ x ∈ S, x * z ∈ commutator H) :
    ∀ b : H, b * z ∈ commutator H ∨ b ∈ commutator H := by
  let N : Subgroup H := commutator H
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  have hπz : π z * π z = 1 := by rw [← map_mul, ← pow_two, hz2, map_one]
  have hpS : ∀ x ∈ S, π x = 1 ∨ π x = π z := by
    intro x hx
    right
    have hxz : x * z ∈ N := hSz x hx
    have h1 : π (x * z) = 1 := (QuotientGroup.eq_one_iff (N := N) (x := x * z)).mpr hxz
    rw [map_mul] at h1
    calc π x = π x * (π z * π z) := by rw [hπz, mul_one]
      _ = (π x * π z) * π z := by rw [mul_assoc]
      _ = 1 * π z := by rw [h1]
      _ = π z := by rw [one_mul]
  intro b
  have hb : π b = 1 ∨ π b = π z := by
    have hb' : b ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top b
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hb'
    · exact hpS
    · left; rw [map_one]
    · intro x y hx hy hx' hy'
      rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
      · left; rw [map_mul, hx', hy', one_mul]
      · right; rw [map_mul, hx', hy', one_mul]
      · right; rw [map_mul, hx', hy', mul_one]
      · left; rw [map_mul, hx', hy', hπz]
    · intro x hx hx'
      rcases hx' with hx' | hx'
      · left; rw [map_inv, hx', inv_one]
      · right; rw [map_inv, hx', inv_eq_of_mul_eq_one_right hπz]
  rcases hb with hb | hb
  · right
    exact (QuotientGroup.eq_one_iff (N := N) (x := b)).mp hb
  · left
    refine (QuotientGroup.eq_one_iff (N := N) (x := b * z)).mp ?_
    change π (b * z) = 1
    rw [map_mul, hb, hπz]

theorem exists_zmodTwoHom_ker_eq_commutator {S : Set H} (hS : Subgroup.closure S = ⊤) {z : H}
    (hz : z ∉ commutator H) (hz2 : z ^ 2 = 1) (hSz : ∀ x ∈ S, x * z ∈ commutator H) :
    ∃ χ : H →* Multiplicative (ZMod 2), χ.ker = commutator H ∧
      χ z = Multiplicative.ofAdd 1 := by
  have hdisj : ∀ b : H, (b * z ∈ commutator H) ∨ (b ∈ commutator H) :=
    mul_mem_commutator_or_mem_commutator_of_closure_eq_top hS hz2 hSz
  have hidx : (commutator H).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    exact ⟨z, hz, hdisj⟩
  obtain ⟨χ, hχker⟩ := CFSG.Holt.exists_monoidHom_ker_eq_of_index_eq_two hidx
  refine ⟨χ, hχker, ?_⟩
  have hzχ : χ z ≠ 1 := by
    intro h
    apply hz
    rw [← hχker]
    exact MonoidHom.mem_ker.mpr h
  have htwo : ∀ u : Multiplicative (ZMod 2), u = 1 ∨ u = Multiplicative.ofAdd 1 := by
    decide
  exact (htwo (χ z)).resolve_left hzχ

end Sign

end CFSG.OddTranspositions.PartThree.ElevenSp

end
