module

public import CFSG.OddTranspositions.PartThree.EightEight.ASNZBase
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared

import CFSG.GroupTheory.InvolutionConjParity
import CFSG.OddTranspositions.BlockCover
import CFSG.OddTranspositions.BlockGraph
import CFSG.OddTranspositions.BlockTransitive
import CFSG.OddTranspositions.PartThree.EightEight.ASBase
import CFSG.OddTranspositions.PartFour.LineTransport
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.OddTranspositions.TheoremTwo.DiffBlock
import CFSG.Mathlib.GroupTheory.SimpleConj
import CFSG.OddTranspositions.PartThree.EightEight.DeltaOrbit
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks
import CFSG.OddTranspositions.PartThree.EightEight.StarBlocks
import CFSG.OddTranspositions.PartThree.EightEight.StarSigma
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.PartThree.EightSeven
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.Timmesfeld.Basic
import CFSG.Timmesfeld.Bridge.Asc72ConjOrbit
import CFSG.CGT.T75E.Lemma26
import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
import CFSG.CGT.Timmesfeld75.Sec4Three
import CFSG.CGT.Timmesfeld75.Sec5FiveEng
import CFSG.CGT.Timmesfeld75.Step511Card
import CFSG.CGT.Timmesfeld75.Step57Reduction
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.Uniqueness.Bender.OddCentralizer
import CFSG.GH74.Uniqueness.Bender.Unitary
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.OddTranspositions.AlmostSimple
import CFSG.OddTranspositions.BlockAction2
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.Disconnected
import CFSG.OddTranspositions.O4PairTenThreeTranspositions
import CFSG.OddTranspositions.Reduction
import CFSG.OddTranspositions.WidthTwoNoProduct
import CFSG.OddTranspositions.WreathQuotient
import CFSG.RankThree.GF2n.Tim79aSec2
import CFSG.RankThree.GF2n.Tim79aSec23Inputs
import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
  CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem starBar_conj_alpha (hC : HypothesisC D) (g q : G) :
    starBar D (hC.conj g).alpha (g * q * g⁻¹) =
      QuotientGroup.congr (CFSG.solvableRadical (Halpha D hC.alpha))
        (CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) (conjEquiv hC g)
        (conjRadical_map hC g) (starBar D hC.alpha q) := by
  by_cases hq : q ∈ Halpha D hC.alpha
  · have hq' : g * q * g⁻¹ ∈ Halpha D (hC.conj g).alpha := by
      rw [← conjEquiv_coe hC g ⟨q, hq⟩]
      exact SetLike.coe_mem _
    rw [starBar_of_mem hq', starBar_of_mem hq, QuotientGroup.congr_mk']
    exact congrArg _ (Subtype.ext (conjEquiv_coe hC g ⟨q, hq⟩).symm)
  · have hq' : g * q * g⁻¹ ∉ Halpha D (hC.conj g).alpha := by
      intro h
      have e := conjEquiv_coe hC g ((conjEquiv hC g).symm ⟨_, h⟩)
      rw [MulEquiv.apply_symm_apply] at e
      change g * q * g⁻¹ = g * _ * g⁻¹ at e
      have hk := SetLike.coe_mem ((conjEquiv hC g).symm ⟨_, h⟩)
      rw [← mul_left_cancel (mul_right_cancel e)] at hk
      exact hq hk
    rw [starBar_of_notMem hq', starBar_of_notMem hq, map_one]

theorem starSocle_conj (hC : HypothesisC D) (g : G) :
    (starSocle D hC.alpha).map (QuotientGroup.congr (CFSG.solvableRadical (Halpha D hC.alpha))
      (CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) (conjEquiv hC g)
        (conjRadical_map hC g)).toMonoidHom = starSocle D (hC.conj g).alpha :=
  CFSG.map_monolith _

theorem mem_starSocle_conj_iff (hC : HypothesisC D) (g : G)
    (a : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :
    QuotientGroup.congr (CFSG.solvableRadical (Halpha D hC.alpha))
        (CFSG.solvableRadical (Halpha D (hC.conj g).alpha)) (conjEquiv hC g)
        (conjRadical_map hC g) a ∈ starSocle D (hC.conj g).alpha ↔
      a ∈ starSocle D hC.alpha := by
  rw [← starSocle_conj hC g]
  exact Subgroup.mem_map_iff_mem (MulEquiv.injective _)

@[expose] def InnerAt (D ρ : Set G) (t : G) : Prop :=
  ∃ j ∈ starSocle D ρ, ∀ h ∈ Halpha D ρ, starBar D ρ (t * h * t⁻¹) = j * starBar D ρ h * j⁻¹

theorem innerAt_conj (hC : HypothesisC D) {t : G} (g : G) (h : InnerAt D hC.alpha t) :
    InnerAt D (hC.conj g).alpha (g * t * g⁻¹) := by
  obtain ⟨j, hj, hall⟩ := h
  refine ⟨_, (mem_starSocle_conj_iff hC g j).mpr hj, fun h' hh' => ?_⟩
  have e := conjEquiv_coe hC g ((conjEquiv hC g).symm ⟨h', hh'⟩)
  rw [MulEquiv.apply_symm_apply] at e
  obtain ⟨k, rfl⟩ : ∃ k : Halpha D hC.alpha, h' = g * k * g⁻¹ := ⟨_, e⟩
  have e2 : g * t * g⁻¹ * (g * k * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * k * t⁻¹) * g⁻¹ := by
    group
  rw [e2, starBar_conj_alpha, starBar_conj_alpha, hall k k.2, map_mul, map_mul, map_inv]

theorem innerAt_conj_iff (hC : HypothesisC D) {t : G} (g : G) :
    InnerAt D (hC.conj g).alpha (g * t * g⁻¹) ↔ InnerAt D hC.alpha t := by
  refine ⟨fun h => ?_, innerAt_conj hC g⟩
  have h' := innerAt_conj (hC.conj g) g⁻¹ h
  have hα : ((hC.conj g).conj g⁻¹).alpha = hC.alpha := by
    rw [HypothesisC.conj_alpha, HypothesisC.conj_alpha, cimg_inv_cimg]
  rwa [hα, show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at h'

theorem innerAt_conj_iff_of_commute (hC : HypothesisC D) {t g : G} (hg : Commute g t) :
    InnerAt D (hC.conj g).alpha t ↔ InnerAt D hC.alpha t := by
  have h := innerAt_conj_iff hC (t := t) g
  rwa [hg.eq, mul_inv_cancel_right] at h

theorem innerAt_cimg_iff_of_commute (hC : HypothesisC D) {ρ : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) {t g : G} (hg : Commute g t) :
    InnerAt D (cimg g ρ) t ↔ InnerAt D ρ t := by
  obtain ⟨h, rfl⟩ := mem_blockClass_iff.mp hρ
  have h1 : ((hC.conj h).conj g).alpha = cimg g (cimg h hC.alpha) := by
    rw [HypothesisC.conj_alpha, HypothesisC.conj_alpha]
  change InnerAt D (cimg g (cimg h hC.alpha)) t ↔ InnerAt D (cimg h hC.alpha) t
  rw [← h1, ← hC.conj_alpha h]
  exact innerAt_conj_iff_of_commute (hC.conj h) hg

theorem innerAt_iff_of_not_commute (hC : HypothesisC D) {t d e : G} {ρ ρ' : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) (hρ' : ρ' ∈ blockClass hC.alpha) (hd : d ∈ ρ) (he : e ∈ ρ')
    (hdt : Commute d t) (het : Commute e t) (hde : ¬ Commute d e) :
    InnerAt D ρ' t ↔ InnerAt D ρ t := by
  have hdD : d ∈ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hρ hd
  have heD : e ∈ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hρ' he
  obtain ⟨ℓ, hℓ, hℓd⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul
    (hC.setup.oddT.mul_self_eq_one hdD) (hC.setup.oddT.mul_self_eq_one heD)
    (hC.setup.oddT.odd_of_not_commute hdD heD hde)
  have hle : Subgroup.closure ({d, e} : Set G) ≤ Subgroup.centralizer {t} := by
    rw [Subgroup.closure_le]
    rintro a (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · exact hdt.eq
    · exact het.eq
  have hℓt : Commute ℓ t := Subgroup.mem_centralizer_singleton_iff.mp (hle hℓ)
  have hcimg : cimg ℓ ρ = ρ' :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha (cimg_mem_blockClass_iff.mpr hρ) hρ'
      ⟨e, ⟨d, hd, hℓd⟩, he⟩
  rw [← hcimg]
  exact innerAt_cimg_iff_of_commute hC hρ hℓt

theorem innerAt_of_starBar_mem {ρ : Set G} {t : G} (ht : t ∈ Halpha D ρ)
    (htJ : starBar D ρ t ∈ starSocle D ρ) : InnerAt D ρ t :=
  ⟨starBar D ρ t, htJ, fun _ hh => starBar_conj ht hh⟩

omit [Finite G] in
theorem mem_centralizer_Halpha_of_mem {ρ : Set G} {b : G} (hb : b ∈ ρ) :
    b ∈ Subgroup.centralizer (Halpha D ρ : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hh =>
    (Subgroup.mem_centralizer_iff.mp (Halpha_le_centralizer D ρ hh) b hb).symm

theorem not_innerAt_mul {ρ : Set G}
    (hcen : Subgroup.centralizer ((starSocle D ρ : Subgroup (Halpha D ρ ⧸
      CFSG.solvableRadical (Halpha D ρ))) : Set (Halpha D ρ ⧸
        CFSG.solvableRadical (Halpha D ρ))) = ⊥)
    {a b : G} (ha : a ∈ Halpha D ρ) (haJ : starBar D ρ a ∉ starSocle D ρ)
    (hb : b ∈ Subgroup.centralizer (Halpha D ρ : Set G)) : ¬ InnerAt D ρ (a * b) := by
  rintro ⟨j, hj, hall⟩
  have hmem : j⁻¹ * starBar D ρ a ∈ Subgroup.centralizer
      ((starSocle D ρ : Subgroup (Halpha D ρ ⧸ CFSG.solvableRadical (Halpha D ρ))) :
        Set (Halpha D ρ ⧸ CFSG.solvableRadical (Halpha D ρ))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k _
    obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical (Halpha D ρ)) k
    have hk := hall k' k'.2
    have hbk : (k' : G) * b = b * k' := Subgroup.mem_centralizer_iff.mp hb k' k'.2
    have e : a * b * k' * (a * b)⁻¹ = a * k' * a⁻¹ := by
      calc a * b * k' * (a * b)⁻¹ = a * (b * k') * b⁻¹ * a⁻¹ := by group
        _ = a * (k' * b) * b⁻¹ * a⁻¹ := by rw [hbk]
        _ = a * k' * a⁻¹ := by group
    rw [e, starBar_conj ha k'.2, starBar_coe] at hk
    calc QuotientGroup.mk' _ k' * (j⁻¹ * starBar D ρ a)
        = j⁻¹ * (j * QuotientGroup.mk' _ k' * j⁻¹) * starBar D ρ a := by group
      _ = j⁻¹ * (starBar D ρ a * QuotientGroup.mk' _ k' * (starBar D ρ a)⁻¹) *
          starBar D ρ a := by rw [← hk]
      _ = j⁻¹ * starBar D ρ a * QuotientGroup.mk' _ k' := by group
  rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact haJ (hmem ▸ hj)

theorem StandingAS.starBar_notMem_starSocle {hC : HypothesisC D} (hSt : StandingAS hC) {p : G}
    (hp : p ∈ DalphaStar D hC.alpha) : starBar D hC.alpha p ∉ starSocle D hC.alpha := by
  intro hpJ
  obtain ⟨c, hc, hcJ⟩ := hSt.exists_notMem_coset hp
  obtain ⟨h, hh, rfl⟩ := hC.Halpha_transitive p hp c hc
  apply hcJ
  rw [starBar_conj hh (mem_Halpha_of_mem_DalphaStar hp)]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hpJ) ((CFSG.monolith_normal _).conj_mem _ hpJ _)


theorem StandingAS.not_innerAt_pow_mul_of_mem_alpha (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ hC.alpha) : ¬ InnerAt D hC.alpha ((x * y * w) ^ n * s) := by
  obtain ⟨-, -, -, hcen, -, -⟩ := hSt.starSocle_spec
  have hzH := mul_mul_pow_mem_Halpha hC hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.1 n
  have hzJ : starBar D hC.alpha ((x * y * w) ^ n) ∉ starSocle D hC.alpha := by
    intro hzJ
    have h1 := hSt.inv_mul_starBar_pow_mem_starSocle h86 h87 hT hn hord
    have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hzJ)
    rw [mul_inv_cancel_right] at h2
    exact hSt.starBar_notMem_starSocle hT.2.2.1 (inv_mem_iff.mp h2)
  exact not_innerAt_mul hcen hzH hzJ (mem_centralizer_Halpha_of_mem hs)

theorem StandingAS.innerAt_pow_mul_of_mem_DalphaStar (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y)
    (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {s : G} (hs : s ∈ DalphaStar D hC.alpha)
    (hsz : Commute s ((x * y * w) ^ n)) : InnerAt D hC.alpha ((x * y * w) ^ n * s) := by
  have hzH := mul_mul_pow_mem_Halpha hC hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.1 n
  have hsH := mem_Halpha_of_mem_DalphaStar hs
  have h1 := hSt.inv_mul_starBar_pow_mem_starSocle h86 h87 hT hn hord
  have h2 := hSt.inv_mul_mem_starSocle_of_commute_starBar_pow h86 h87 hT hn hord hs
    (starBar_commute hsH hzH hsz)
  have hxx := hSt.mul_self_eq_one_of_mem_imageClass (starBar_mem_imageClass hC hT.2.2.1)
  refine innerAt_of_starBar_mem (Subgroup.mul_mem _ hzH hsH) ?_
  rw [starBar_mul hzH hsH]
  set a := starBar D hC.alpha x
  have e : starBar D hC.alpha ((x * y * w) ^ n) * starBar D hC.alpha s =
      a * (a⁻¹ * starBar D hC.alpha ((x * y * w) ^ n)) * a⁻¹ * (a * a) *
        (a⁻¹ * starBar D hC.alpha s) := by group
  rw [e, hxx, mul_one]
  exact Subgroup.mul_mem _ ((CFSG.monolith_normal _).conj_mem _ h1 _) h2

theorem StandingAS.exists_conj_alpha_eq_of_mem_starSigma (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starSigma D x w y n) {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) (hsρ : s ∈ ρ) :
    ∃ g : G, (hC.conj g).alpha = ρ ∧ IsStarTriangle (hC.conj g) x w y := by
  have hU : s ∈ ⋃₀ perpBlocks D hC.alpha (conjOrbit (localGroup D ((x * y * w) ^ n)) x) := by
    rw [← setOf_centSet_notMem_eq_sUnion h86 h87 hC hSt.rad hSt.not_o4 hSt.faithful
      hSt.derivedSeries_ne hT.1 hn hord]
    exact hs
  obtain ⟨σ, hσP, hsσ⟩ := Set.mem_sUnion.mp hU
  have hσρ : σ = ρ := eq_of_mem_of_mem_blockClass hC.isBlock_alpha hσP.1 hρ ⟨s, hsσ, hsρ⟩
  subst hσρ
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hσP.1
  exact ⟨g, (hC.conj_alpha g).trans hg.symm,
    isStarTriangle_conj_of_mem_perpBlocks hC hT hn hord hσP hg⟩

theorem StandingAS.not_innerAt_pow_mul_of_mem_block (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s : G}
    (hs : s ∈ starSigma D x w y n) {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) (hsρ : s ∈ ρ) :
    ¬ InnerAt D ρ ((x * y * w) ^ n * s) := by
  obtain ⟨g, hgα, hT'⟩ := hSt.exists_conj_alpha_eq_of_mem_starSigma h86 h87 hT hn hord hs hρ hsρ
  have hs' : s ∈ (hC.conj g).alpha := by
    rw [hgα]
    exact hsρ
  have h := (hSt.conj g).not_innerAt_pow_mul_of_mem_alpha h86 h87 hT' hn hord hs'
  rwa [hgα] at h

theorem StandingAS.innerAt_pow_mul_of_commute_of_notMem (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {p s : G}
    (hp : p ∈ starSigma D x w y n) (hs : s ∈ starSigma D x w y n) (hps : Commute p s)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) (hpρ : p ∈ ρ) (hsρ : s ∉ ρ) :
    InnerAt D ρ ((x * y * w) ^ n * s) := by
  obtain ⟨g, hgα, hT'⟩ := hSt.exists_conj_alpha_eq_of_mem_starSigma h86 h87 hT hn hord hp hρ hpρ
  obtain ⟨β, hβ, hsβ⟩ := exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hs.1.1
  have hρβ : ρ ≠ β := by
    rintro rfl
    exact hsρ hsβ
  have hsS : s ∈ DalphaStar D (hC.conj g).alpha := by
    rw [hgα]
    exact ⟨β, mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hρ hβ
      hρβ hpρ hsβ hps, hsβ⟩
  have h := (hSt.conj g).innerAt_pow_mul_of_mem_DalphaStar h86 h87 hT' hn hord hsS hs.1.2
  rwa [hgα] at h


theorem StandingAS.not_commute_of_mem_starGamma (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {s c p : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) (hc : c ∈ starGamma hC x w y n s)
    (hp : p ∈ starN D hC.alpha (starSigma D x w y n)) (hps : p ≠ s) : ¬ Commute p s := by
  intro hcomm
  obtain ⟨ρs, hρs, hsρs⟩ := hs.2
  obtain ⟨ρp, hρp, hpρp⟩ := hp.2
  have hρs' : ρs ∈ blockClass hC.alpha := hρs.1
  have hρp' : ρp ∈ blockClass hC.alpha := hρp.1
  have hpρs : p ∉ ρs := fun h => not_commute_of_mem_of_mem h86 h87 hC hSt.rad hSt.not_o4
    hSt.faithful hSt.derivedSeries_ne hρs' h hsρs hps hcomm
  have hsρp : s ∉ ρp := by
    intro h
    have hρ : ρp = ρs := eq_of_mem_of_mem_blockClass hC.isBlock_alpha hρp' hρs' ⟨s, h, hsρs⟩
    rw [hρ] at hpρp
    exact hpρs hpρp
  have hin := hSt.innerAt_pow_mul_of_commute_of_notMem h86 h87 hT hn hord hp.1 hs.1 hcomm hρp'
    hpρp hsρp
  have hout := hSt.not_innerAt_pow_mul_of_mem_block h86 h87 hT hn hord hs.1 hρs' hsρs
  obtain ⟨hk, -, -, -, -⟩ := hSt.orderOf_mul_of_mem_starGamma h86 h87 hT hn hord hs hc
  have hsD : s ∈ D := hs.1.1.1
  have hcD : c ∈ D := DalphaStar_subset hC.isBlock_alpha hc.1
  have hss := hC.setup.oddT.mul_self_eq_one hsD
  have hcc := hC.setup.oddT.mul_self_eq_one hcD
  have hodd : Odd (orderOf (s * c)) := by
    have e : (c * s)⁻¹ = s * c := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hss, inv_eq_of_mul_eq_one_right hcc]
    rwa [← e, orderOf_inv]
  obtain ⟨ℓ, hℓ, hℓs⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul hss hcc hodd
  have hle : Subgroup.closure ({s, c} : Set G) ≤
      Subgroup.centralizer {(x * y * w) ^ n * s} := by
    rw [Subgroup.closure_le]
    rintro a (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    · exact (hs.1.1.2.mul_right (Commute.refl _)).eq
    · exact hc.2.2.eq
  have hℓτ : Commute ℓ ((x * y * w) ^ n * s) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hℓ)
  have hcρ : c ∈ cimg ℓ ρs := ⟨s, hsρs, hℓs⟩
  have hout' : ¬ InnerAt D (cimg ℓ ρs) ((x * y * w) ^ n * s) := by
    rw [innerAt_cimg_iff_of_commute hC hρs' hℓτ]
    exact hout
  have hpτ : Commute p ((x * y * w) ^ n * s) := hp.1.1.2.mul_right hcomm
  have hpc : Commute p c := by
    by_contra hpc
    exact hout' ((innerAt_iff_of_not_commute hC hρp' (cimg_mem_blockClass_iff.mpr hρs') hpρp
      hcρ hpτ hc.2.2 hpc).mpr hin)
  exact hSt.not_commute_of_mem_starN h86 h87 hT hn hord hp hc.1 hc.2.1 hpc.symm

theorem conj_mem_starN (hC : HypothesisC D) {x w y : G} {n : ℕ} {b s : G}
    (hb : b ∈ starN D hC.alpha (starSigma D x w y n))
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) :
    b * s * b⁻¹ ∈ starN D hC.alpha (starSigma D x w y n) := by
  have hbK : b ∈ localGroup D ((x * y * w) ^ n) := mem_localGroup_of_mem hb.1.1
  refine ⟨⟨⟨hC.setup.normal b s hs.1.1.1, ?_⟩, fun h => hs.1.2 ?_⟩,
    (Halpha_le_normalizer hC.setup.normal (mem_Halpha_of_mem_DalphaStar hb.2) s).mp hs.2⟩
  · have h := hs.1.1.2.conj b
    rwa [hb.1.1.2.eq, mul_inv_cancel_right] at h
  · have h2 := conj_mem_conjOrbit (Subgroup.inv_mem _ hbK) h
    rwa [show b⁻¹ * (b * s * b⁻¹) * b⁻¹⁻¹ = s by group] at h2

theorem StandingAS.conj_mem_starGamma (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {b s c : G}
    (hb : b ∈ starN D hC.alpha (starSigma D x w y n)) (hc : c ∈ starGamma hC x w y n s) :
    b * c * b⁻¹ ∈ starGamma hC x w y n (b * s * b⁻¹) := by
  have hbH := mem_Halpha_of_mem_DalphaStar hb.2
  have hcH := mem_Halpha_of_mem_DalphaStar hc.1
  have hzH := mul_mul_pow_mem_Halpha hC hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.1 n
  refine ⟨(Halpha_le_normalizer hC.setup.normal hbH c).mp hc.1, fun h => hc.2.1 ?_, ?_⟩
  · set π := QuotientGroup.mk' (starSocle D hC.alpha) with hπ
    have hbx : π (starBar D hC.alpha x) = π (starBar D hC.alpha b) :=
      QuotientGroup.eq.mpr (hSt.inv_mul_mem_starSocle_of_commute_starBar_pow h86 h87 hT hn hord
        hb.2 (starBar_commute hbH hzH hb.1.1.2))
    have h' : π (starBar D hC.alpha x) = π (starBar D hC.alpha (b * c * b⁻¹)) :=
      QuotientGroup.eq.mpr h
    rw [starBar_conj hbH hcH, map_mul, map_mul, map_inv, ← hbx] at h'
    have h2 : π (starBar D hC.alpha x) * π (starBar D hC.alpha c) =
        π (starBar D hC.alpha x) * π (starBar D hC.alpha x) := by
      calc π (starBar D hC.alpha x) * π (starBar D hC.alpha c)
          = π (starBar D hC.alpha x) * π (starBar D hC.alpha c) *
              (π (starBar D hC.alpha x))⁻¹ * π (starBar D hC.alpha x) := by group
        _ = π (starBar D hC.alpha x) * π (starBar D hC.alpha x) := by rw [← h']
    exact QuotientGroup.eq.mp (mul_left_cancel h2).symm
  · set z := (x * y * w) ^ n with hz
    have e : z * (b * s * b⁻¹) = b * (z * s) * b⁻¹ := by
      calc z * (b * s * b⁻¹) = z * b * s * b⁻¹ := by group
        _ = b * z * s * b⁻¹ := by rw [hb.1.1.2.eq]
        _ = b * (z * s) * b⁻¹ := by group
    rw [e]
    exact hc.2.2.conj b

theorem StandingAS.conj_mem_starN_and_starGamma_nonempty_of_mem_closure (h86 : Lemma8_6)
    (h87 : Theorem8_7) {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {ℓ : G}
    (hℓ : ℓ ∈ Subgroup.closure (starN D hC.alpha (starSigma D x w y n))) {s : G}
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n))
    (hΓ : (starGamma hC x w y n s).Nonempty) :
    ℓ * s * ℓ⁻¹ ∈ starN D hC.alpha (starSigma D x w y n) ∧
      (starGamma hC x w y n (ℓ * s * ℓ⁻¹)).Nonempty := by
  suffices key : ∀ t : G, t ∈ starN D hC.alpha (starSigma D x w y n) →
      (starGamma hC x w y n t).Nonempty →
      ℓ * t * ℓ⁻¹ ∈ starN D hC.alpha (starSigma D x w y n) ∧
        (starGamma hC x w y n (ℓ * t * ℓ⁻¹)).Nonempty from key s hs hΓ
  clear hs hΓ
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hℓ
  · intro b hb s hs hΓ
    obtain ⟨c, hc⟩ := hΓ
    exact ⟨conj_mem_starN hC hb hs, ⟨_, hSt.conj_mem_starGamma h86 h87 hT hn hord hb hc⟩⟩
  · intro b hb s hs hΓ
    have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hC.setup.oddT.mul_self_eq_one hb.1.1.1)
    have e : b⁻¹ * s * b⁻¹⁻¹ = b * s * b⁻¹ := by rw [inv_inv, hbb]
    obtain ⟨c, hc⟩ := hΓ
    rw [e]
    exact ⟨conj_mem_starN hC hb hs, ⟨_, hSt.conj_mem_starGamma h86 h87 hT hn hord hb hc⟩⟩
  · intro s hs hΓ
    rw [one_mul, inv_one, mul_one]
    exact ⟨hs, hΓ⟩
  · intro a b _ _ ha hb s hs hΓ
    obtain ⟨h1, h2⟩ := hb s hs hΓ
    rw [show a * b * s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ by group]
    exact ha _ h1 h2

theorem StandingAS.starGamma_nonempty (h86 : Lemma8_6) (h87 : Theorem8_7) {hC : HypothesisC D}
    (hSt : StandingAS hC) {x w y : G} {n : ℕ} (hT : IsStarTriangle hC x w y) (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {p : G}
    (hp : p ∈ starN D hC.alpha (starSigma D x w y n)) : (starGamma hC x w y n p).Nonempty := by
  obtain ⟨c, hc, hcJ⟩ := hSt.exists_notMem_coset hT.2.2.1
  obtain ⟨s₀, ⟨hs₀, hcs₀⟩, -⟩ := hSt.existsUnique_mem_starGamma h86 h87 hT hn hord hc hcJ
  by_cases hps : p = s₀
  · rw [hps]
    exact ⟨c, hcs₀⟩
  have hnc := hSt.not_commute_of_mem_starGamma h86 h87 hT hn hord hs₀ hcs₀ hp hps
  have hpD : p ∈ D := hp.1.1.1
  have hs₀D : s₀ ∈ D := hs₀.1.1.1
  obtain ⟨ℓ, hℓ, hℓs⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul
    (hC.setup.oddT.mul_self_eq_one hs₀D) (hC.setup.oddT.mul_self_eq_one hpD)
    (hC.setup.oddT.odd_of_not_commute hs₀D hpD fun h => hnc h.symm)
  have hle : Subgroup.closure ({s₀, p} : Set G) ≤
      Subgroup.closure (starN D hC.alpha (starSigma D x w y n)) := by
    apply Subgroup.closure_mono
    rintro a (rfl | rfl)
    · exact hs₀
    · exact hp
  have h := (hSt.conj_mem_starN_and_starGamma_nonempty_of_mem_closure h86 h87 hT hn hord (hle hℓ)
    hs₀ ⟨c, hcs₀⟩).2
  rwa [hℓs] at h

theorem StandingAS.not_commute_of_mem_starN_of_ne (h86 : Lemma8_6) (h87 : Theorem8_7)
    {hC : HypothesisC D} (hSt : StandingAS hC) {x w y : G} {n : ℕ}
    (hT : IsStarTriangle hC x w y) (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {p s : G}
    (hp : p ∈ starN D hC.alpha (starSigma D x w y n))
    (hs : s ∈ starN D hC.alpha (starSigma D x w y n)) (hps : p ≠ s) : ¬ Commute p s := by
  obtain ⟨c, hc⟩ := hSt.starGamma_nonempty h86 h87 hT hn hord hs
  exact hSt.not_commute_of_mem_starGamma h86 h87 hT hn hord hs hc hp hps

end CFSG.OddTranspositions.PartThree.EightEight

end
