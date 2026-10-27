module

public import CFSG.OddTranspositions.PartThree.Twelve.SixComponent
public import CFSG.OddTranspositions.PartFour.Fourteen.UnitaryCommonPerp
import CFSG.OddTranspositions.PartThree.Twelve.Five
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockUnitary
import CFSG.OddTranspositions.PartFour.Fourteen.UnitaryShapeRigid
import CFSG.OddTranspositions.PartFour.Fourteen.SpShapeRigid
import CFSG.OddTranspositions.PartFour.Fourteen.ShapeTransport
import CFSG.OddTranspositions.PartThree.Twelve.FourOrth
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.Quasithin.Background.E1TwoAbs
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Hom
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
import CFSG.LocalAnalysis.EvenSporadicStandard.SolvableRadical
import CFSG.OddTranspositions.WidthSylow
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAlignImagesSwap
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.Connectivity
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

section UnitaryShape

variable {X : Type} [Group X]

theorem isSimpleGroup_and_isPerfect_of_isUnitaryTransvection {s : X} {k f : ℕ} (hk : 2 ≤ k)
    (hf : 2 ≤ f) (h : IsUnitaryTransvection X k f s) :
    IsSimpleGroup (X ⧸ Subgroup.center X) ∧ Group.IsPerfect (X ⧸ Subgroup.center X) := by
  have h' := h
  obtain ⟨F, _, _, hF, e, -⟩ := h
  have hperf := isPerfect_statedProj_statedSU hF hk hf
  refine ⟨?_, Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩
  have h4f : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · obtain ⟨j, hj, F₀, _, _, hF₀, e₀, -⟩ := isSymplecticTransvection_of_isUnitaryTransvection_two h'
    have h4 : 4 ≤ Nat.card F₀ := by rw [hF₀]; exact h4f
    have : Fintype F₀ := Fintype.ofFinite F₀
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP F₀ 2 :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF₀])
    have := CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le (n := j) h4
      (by omega)
    exact MulEquiv.isSimpleGroup e₀
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 f hF k hk3
      fun h => by have := (Prod.mk.inj h).2; omega
    exact MulEquiv.isSimpleGroup e

theorem solvableRadical_eq_center_of_isUnitaryTransvection [Finite X] {s : X} {k f : ℕ}
    (hk : 2 ≤ k) (hf : 2 ≤ f) (h : IsUnitaryTransvection X k f s) :
    CFSG.solvableRadical X = Subgroup.center X := by
  obtain ⟨hsimp, hperf⟩ := isSimpleGroup_and_isPerfect_of_isUnitaryTransvection hk hf h
  refine le_antisymm ?_ (CFSG.OddTranspositions.center_le_solvableRadical X)
  have hrad : CFSG.solvableRadical (X ⧸ Subgroup.center X) = ⊥ :=
    CFSG.solvableRadical_eq_bot_of_isSimpleGroup _ (by
      by_contra hab
      push Not at hab
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨hab⟩⟩)
  have hle := CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical_le
    (ρ := QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
  rw [hrad, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hle
  exact hle

theorem isUnitaryTransvection_quotient_solvableRadical [Finite X] {s : X} {k f : ℕ}
    (hk : 2 ≤ k) (hf : 2 ≤ f) (h : IsUnitaryTransvection X k f s) :
    IsUnitaryTransvection (X ⧸ CFSG.solvableRadical X) k f (QuotientGroup.mk s) ∧
      Subgroup.center (X ⧸ CFSG.solvableRadical X) = ⊥ ∧ ¬ Group.IsSolvable X := by
  obtain ⟨hsimp, hperf⟩ := isSimpleGroup_and_isPerfect_of_isUnitaryTransvection hk hf h
  have hSZ := solvableRadical_eq_center_of_isUnitaryTransvection hk hf h
  let ε : X ⧸ CFSG.solvableRadical X ≃* X ⧸ Subgroup.center X :=
    QuotientGroup.quotientMulEquivOfEq hSZ
  have hnc : ¬ ∀ a b : X ⧸ Subgroup.center X, a * b = b * a := fun hab =>
    Group.IsPerfect.not_isMulCommutative _ ⟨⟨hab⟩⟩
  have hZ : Subgroup.center (X ⧸ CFSG.solvableRadical X) = ⊥ := by
    have : IsSimpleGroup (X ⧸ CFSG.solvableRadical X) := MulEquiv.isSimpleGroup ε
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (X ⧸ CFSG.solvableRadical X))
      with h1 | h1
    · exact h1
    · exfalso
      apply hnc
      intro a b
      have ha : ε.symm a ∈ Subgroup.center (X ⧸ CFSG.solvableRadical X) := h1 ▸ Subgroup.mem_top _
      apply ε.symm.injective
      rw [map_mul, map_mul]
      exact (Subgroup.mem_center_iff.mp ha (ε.symm b)).symm
  refine ⟨?_, hZ, fun hsol => ?_⟩
  · obtain ⟨F, hFf, hFin, hF, e, hr⟩ := h
    refine ⟨F, hFf, hFin, hF,
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans ε).trans e,
      ?_⟩
    exact hr
  · have : Group.IsSolvable (X ⧸ Subgroup.center X) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (Subgroup.center X))
    exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect this

end UnitaryShape

section Pivot

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem ne_five_one_of_two_le {n f : ℕ} (hf : 2 ≤ f) : (n, f) ≠ (5, 1) := fun h => by
  have := (Prod.mk.inj h).2
  omega

theorem exists_conj_deltaIn_u (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    {δ δ' : Subgroup.closure Ω} (hδ : δ ∈ deltaIn Ω D x y hC.d)
    (hδ' : δ' ∈ deltaIn Ω D x y hC.d) :
    ∃ g ∈ Subgroup.closure (deltaIn Ω D x y hC.d), g * δ * g⁻¹ = δ' := by
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨t, ht, -, -, -, -, hcl⟩ := isUnitaryTransvection_closure_commonCommute hZ hn
    (ne_five_one_of_two_le hf) hU
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hx, rfl⟩)
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hy, rfl⟩)
    (not_commute_mk_of_mem_commSet hC hMZ hα hx hy hxy)
  have hne := (subset_rootBlock_and_ne_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs
    hn hU).2
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs hne
  let δH : Halpha D hC.alpha := ⟨δ, mem_Halpha_of_mem_commSet hC hα hδ.2⟩
  let δH' : Halpha D hC.alpha := ⟨δ', mem_Halpha_of_mem_commSet hC hα hδ'.2⟩
  have hδH : δH ∈ commonPerpH hC x y := hδ
  have hδH' : δH' ∈ commonPerpH hC x y := hδ'
  have himg := image_commonPerpH hC hMZ hα hs hx hy hxy
  have hm1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) δH ∈
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) '' commonPerpH hC x y :=
    ⟨δH, hδH, rfl⟩
  have hm2 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) δH' ∈
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) '' commonPerpH hC x y :=
    ⟨δH', hδH', rfl⟩
  rw [himg] at hm1 hm2
  obtain ⟨g₁, hg₁, he₁⟩ := (hcl _).mp hm1
  obtain ⟨g₂, hg₂, he₂⟩ := (hcl _).mp hm2
  have hgbar : g₂ * g₁⁻¹ ∈ Subgroup.closure {z | IsConj s z ∧
      Commute z (QuotientGroup.mk' _ ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩) ∧
      Commute z (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩)} :=
    Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁)
  rw [← map_closure_commonPerpH hC hMZ hα hs hx hy hxy] at hgbar
  obtain ⟨g₀, hg₀, hg₀e⟩ := hgbar
  have hconj : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (g₀ * δH * g₀⁻¹) =
      QuotientGroup.mk' _ δH' := by
    rw [map_mul, map_mul, map_inv, hg₀e, ← he₁, ← he₂]
    group
  have hδs : δH ∈ DstarH hC := mem_DstarH_of_mem_commSet hC hα hδ.2
  have hδs' : δH' ∈ DstarH hC := mem_DstarH_of_mem_commSet hC hα hδ'.2
  have heq : g₀ * δH * g₀⁻¹ = δH' := hinj (DstarH_conj_mem hC hδs) hδs' hconj
  obtain ⟨g, hg, hgeq⟩ := exists_mem_closure_deltaIn_of_mem_closure_commonPerpH hC hα hΔΩ hg₀
  refine ⟨g, hg, Subtype.ext ?_⟩
  have := congrArg Subtype.val heq
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
  rw [hgeq]
  exact this

theorem DalphaStar_barSet_eq_of_trans (hC : HypothesisC D) {x y : G} {Ω : Set G}
    (hΩ : Ω ⊆ commSet D x ∩ commSet D y) (hdΩ : hC.d ∈ Ω)
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    (htrans : ∀ δ δ' : Subgroup.closure Ω, δ ∈ deltaIn Ω D x y hC.d →
      δ' ∈ deltaIn Ω D x y hC.d →
        ∃ g ∈ Subgroup.closure (deltaIn Ω D x y hC.d), g * δ * g⁻¹ = δ')
    (hcen : CFSG.solvableRadical (Subgroup.closure Ω) ≤ Subgroup.center (Subgroup.closure Ω))
    (hS : Setup (Subgroup.closure Ω) (inClosure Ω))
    (hns : ¬ Group.IsSolvable (Subgroup.closure Ω))
    (hCL : HypothesisC (barSet Ω))
    (hd : hCL.d = QuotientGroup.mk' _ ⟨hC.d, Subgroup.subset_closure hdΩ⟩) :
    DalphaStar (barSet Ω) hCL.alpha =
      QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω)) '' deltaIn Ω D x y hC.d := by
  have hnc := exists_not_commute_of_setup hS hns
  have hcomm := commSet_image_inClosure hC.setup.oddT hΩ hdΩ hΔΩ hcen hnc
  rw [hCL.DalphaStar_alpha]
  have hE := hCL.hE
  rw [hd] at hE
  rw [eq_commSet_of_isMaxOrbit hCL.setup.normal ?_ hE, hcomm]
  intro e he e' he'
  rw [hcomm] at he he'
  obtain ⟨δ, hδ, rfl⟩ := he
  obtain ⟨δ', hδ', rfl⟩ := he'
  obtain ⟨g, hg, hgeq⟩ := htrans δ δ' hδ hδ'
  refine ⟨QuotientGroup.mk' _ g, ?_, ?_⟩
  · rw [hcomm, ← MonoidHom.map_closure]
    exact ⟨g, hg, rfl⟩
  · rw [← hgeq, map_mul, map_mul, map_inv]

theorem not_isSolvable_closure_of_subset_u (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω) :
    ¬ Group.IsSolvable (Subgroup.closure Ω) := by
  obtain ⟨t, ht, -, -, -, hUK, -⟩ := isUnitaryTransvection_closure_commonCommute
    (center_Hbar_eq_bot hC) hn (ne_five_one_of_two_le hf) hU
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hx, rfl⟩)
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hy, rfl⟩)
    (not_commute_mk_of_mem_commSet hC hMZ hα hx hy hxy)
  have hKbar := (isUnitaryTransvection_quotient_solvableRadical (by omega) hf hUK).2.2
  intro hL
  apply hKbar
  rw [← map_closure_commonPerpH hC hMZ hα hs hx hy hxy]
  have hle : Subgroup.closure (commonPerpH hC x y) ≤
      (Subgroup.closure Ω).comap (Halpha D hC.alpha).subtype := by
    rw [Subgroup.closure_le]
    intro z hz
    exact Subgroup.subset_closure (hΔΩ hz)
  let φ : Subgroup.closure (commonPerpH hC x y) →* Subgroup.closure Ω :=
    ((Halpha D hC.alpha).subtype.comp (Subgroup.closure (commonPerpH hC x y)).subtype).codRestrict
      _ fun k => hle k.2
  have hφ : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.closure Ω => (z : G)) h
  have : Group.IsSolvable (Subgroup.closure (commonPerpH hC x y)) :=
    Group.isSolvable_of_isSolvable_injective hφ
  exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective _ _)

theorem exists_mulEquiv_quotRad_of_surjective {K A B : Type} [Group K] [Group A] [Group B]
    [Finite K] {φ : K →* A} {χ : K →* B} (hφ : Function.Surjective φ)
    (hφk : Group.IsSolvable φ.ker) (hχ : Function.Surjective χ) (hχk : Group.IsSolvable χ.ker) :
    ∃ Ψ : B ⧸ CFSG.solvableRadical B ≃* A ⧸ CFSG.solvableRadical A,
      ∀ k, Ψ (QuotientGroup.mk' _ (χ k)) = QuotientGroup.mk' _ (φ k) := by
  have : Finite A := Finite.of_surjective φ hφ
  have : Finite B := Finite.of_surjective χ hχ
  obtain ⟨ψ₁, h₁⟩ := CFSG.Quasithin.E1.exists_quotRadEquiv φ hφ hφk
  obtain ⟨ψ₂, h₂⟩ := CFSG.Quasithin.E1.exists_quotRadEquiv χ hχ hχk
  refine ⟨ψ₂.symm.trans ψ₁, fun k => ?_⟩
  rw [MulEquiv.trans_apply, ← h₂, MulEquiv.symm_apply_apply, h₁]

end Pivot

section PivotG4

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem hypothesisE_barSet_u (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΩ : Ω ⊆ commSet D x ∩ commSet D y) (hdΩ : hC.d ∈ Ω)
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    (hcen : CFSG.solvableRadical (Subgroup.closure Ω) ≤ Subgroup.center (Subgroup.closure Ω))
    (hS : Setup (Subgroup.closure Ω) (inClosure Ω))
    (hns : ¬ Group.IsSolvable (Subgroup.closure Ω))
    (hCL : HypothesisC (barSet Ω))
    (hd : hCL.d = QuotientGroup.mk' _ ⟨hC.d, Subgroup.subset_closure hdΩ⟩) :
    (∃ s' ∈ imageClass hCL, IsUnitaryTransvection
      (Halpha (barSet Ω) hCL.alpha ⧸
        CFSG.solvableRadical (Halpha (barSet Ω) hCL.alpha)) (n - 2) f s') ∧
    CFSG.solvableRadical (Halpha (barSet Ω) hCL.alpha) ≤
      Subgroup.center (Halpha (barSet Ω) hCL.alpha) := by
  classical
  have hDal := DalphaStar_barSet_eq_of_trans hC hΩ hdΩ hΔΩ
    (fun δ δ' hδ hδ' => exists_conj_deltaIn_u hC hMZ hα hs hn hf hU hx hy hxy hΔΩ hδ hδ') hcen hS
    hns hCL hd
  have hHL : ((QuotientGroup.mk' (CFSG.solvableRadical (Subgroup.closure Ω))).comp
      (Subgroup.inclusion (tripleGroup_le_closure hΔΩ))).range = Halpha (barSet Ω) hCL.alpha := by
    rw [range_mk_comp_inclusion_closure hΔΩ, MonoidHom.map_closure]
    show _ = Subgroup.closure (DalphaStar _ hCL.alpha)
    rw [hDal]
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨t, ht, hts, htu, htw, hUK, -⟩ := isUnitaryTransvection_closure_commonCommute hZ hn
    (ne_five_one_of_two_le hf) hU
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hx, rfl⟩)
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hy, rfl⟩)
    (not_commute_mk_of_mem_commSet hC hMZ hα hx hy hxy)
  have hKbar : ((QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))).comp
      (Subgroup.inclusion (tripleGroup_le_Halpha hC hα x y))).range =
      Subgroup.closure {z | IsConj s z ∧
        Commute z (QuotientGroup.mk' _ ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩) ∧
        Commute z (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩)} := by
    rw [range_mk_comp_inclusion_H hC hα, map_closure_commonPerpH hC hMZ hα hs hx hy hxy]
  obtain ⟨φ, hφs, hφk, hφa⟩ := exists_surjective_of_range_eq _ hHL
  obtain ⟨χ, hχs, hχk, hχa⟩ := exists_surjective_of_range_eq _ hKbar
  have hφks : Group.IsSolvable φ.ker := by
    rw [hφk]
    exact isSolvable_ker_mk_comp _ (Subgroup.inclusion_injective _) _
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hχks : Group.IsSolvable χ.ker := by
    rw [hχk]
    exact isSolvable_ker_mk_comp _ (Subgroup.inclusion_injective _) _
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_quotRad_of_surjective hφs hφks hχs hχks
  have hUK' := (isUnitaryTransvection_quotient_solvableRadical (by omega) hf hUK).1
  have hSZ := solvableRadical_eq_center_of_isUnitaryTransvection (by omega) hf hUK
  refine ⟨⟨Ψ (QuotientGroup.mk ⟨t, ht⟩), ?_, isUnitaryTransvection_map Ψ hUK'⟩, ?_⟩
  · have hmem : t ∈ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ''
        commonPerpH hC x y := by
      rw [image_commonPerpH hC hMZ hα hs hx hy hxy]
      exact ⟨hts, htu, htw⟩
    obtain ⟨w, hw, hwt⟩ := hmem
    let k₀ : tripleGroup D x y hC.d := ⟨(w : G), Subgroup.subset_closure hw⟩
    have hχk₀ : χ k₀ = ⟨t, ht⟩ := Subtype.ext (by rw [hχa]; exact hwt)
    have h1 : Ψ (QuotientGroup.mk ⟨t, ht⟩) = QuotientGroup.mk' _ (φ k₀) := by
      rw [← hΨ, hχk₀]
      rfl
    rw [h1]
    refine ⟨φ k₀, ?_, rfl⟩
    rw [mem_DstarH_iff, hφa]
    show _ ∈ DalphaStar (barSet Ω) hCL.alpha
    rw [hDal]
    exact ⟨Subgroup.inclusion (tripleGroup_le_closure hΔΩ) k₀, hw, rfl⟩
  · have hne := (subset_rootBlock_and_ne_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs
      hn hU).2
    have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs hne
    have hKd : tripleGroup D x y hC.d ≤ Subgroup.centralizer {hC.d} := by
      rw [Subgroup.closure_le]
      intro z hz
      exact Subgroup.mem_centralizer_singleton_iff.mpr hz.2.2.1.eq
    have hKc : CFSG.solvableRadical (tripleGroup D x y hC.d) ≤
        Subgroup.center (tripleGroup D x y hC.d) := by
      intro k hk
      have hχc : χ k ∈ Subgroup.center _ := by
        rw [← hSZ]
        exact CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical_le hχs
          ⟨k, hk, rfl⟩
      have hgen : Subgroup.closure {g : tripleGroup D x y hC.d |
          (g : G) ∈ commSet D x ∩ commSet D y ∩ commSet D hC.d} = ⊤ :=
        Subgroup.closure_preimage_eq_top _
      have hle : Subgroup.closure {g : tripleGroup D x y hC.d |
          (g : G) ∈ commSet D x ∩ commSet D y ∩ commSet D hC.d} ≤ Subgroup.centralizer {k} := by
        rw [Subgroup.closure_le]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        have hkd : Commute (k : G) hC.d := Subgroup.mem_centralizer_singleton_iff.mp (hKd k.2)
        have hc1 : (k : G) * g * (k : G)⁻¹ ∈ commSet D hC.d :=
          conj_mem_commSet_of_commute hC.setup.normal hkd hg.2
        have h2 : χ (k * g * k⁻¹) = χ g := by
          rw [map_mul, map_mul, map_inv, (Subgroup.mem_center_iff.mp hχc (χ g)).symm,
            mul_inv_cancel_right]
        have h3 := congrArg Subtype.val h2
        rw [hχa, hχa] at h3
        have h4 := hinj (mem_DstarH_of_mem_commSet hC hα hc1)
          (mem_DstarH_of_mem_commSet hC hα hg.2) h3
        have h5 : (k : G) * g * (k : G)⁻¹ = g := congrArg Subtype.val h4
        apply Subtype.ext
        show (g : G) * k = k * g
        calc (g : G) * k = ((k : G) * g * (k : G)⁻¹) * k := by rw [h5]
          _ = k * g := by group
      rw [hgen] at hle
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
    exact solvableRadical_le_center_of_surjective hφs hφks hKc

theorem eq_four_and_exists_isOrthReflection_barSet_u (hIH : Theorem4Below (Nat.card G))
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΩ : Ω ⊆ commSet D x ∩ commSet D y) (hdΩ : hC.d ∈ Ω)
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    (hcen : CFSG.solvableRadical (Subgroup.closure Ω) ≤ Subgroup.center (Subgroup.closure Ω))
    (hS : Setup (Subgroup.closure Ω) (inClosure Ω))
    (hns : ¬ Group.IsSolvable (Subgroup.closure Ω))
    (hCL : HypothesisC (barSet Ω))
    (hd : hCL.d = QuotientGroup.mk' _ ⟨hC.d, Subgroup.subset_closure hdΩ⟩) :
    n = 4 ∧ ∃ t ∈ barSet Ω, IsOrthReflection
      (Subgroup.closure Ω ⧸ CFSG.solvableRadical (Subgroup.closure Ω)) 4 f t := by
  obtain ⟨⟨s', hs', hU'⟩, hMZL⟩ :=
    hypothesisE_barSet_u hC hMZ hα hs hn hf hU hx hy hxy hΩ hdΩ hΔΩ hcen hS hns hCL hd
  have hZL := center_Hbar_eq_bot hCL
  have hE : HypothesisE hCL := Or.inl ⟨s', hs', n - 2, f, by omega, hf, Or.inr (Or.inl hU')⟩
  have hO4 : ¬ ∃ s₀ ∈ imageClass hCL, ∃ f₀ : ℕ, 2 ≤ f₀ ∧ IsOrthReflection
      (Halpha (barSet Ω) hCL.alpha ⧸
        CFSG.solvableRadical (Halpha (barSet Ω) hCL.alpha)) 4 f₀ s₀ := by
    rintro ⟨s₀, -, f₀, -, h₀⟩
    refine notMem_commutator_of_isOrthReflection hZL h₀ ?_
    rw [(isPerfect_of_isUnitaryTransvection hZL (by omega) hf hU').commutator_eq_top]
    exact Subgroup.mem_top s₀
  have hcls := imageClass_isClass hCL
  rcases hIH _ _ hCL (card_quotient_closure_lt hΩ hxy) rad_quotient_solvableRadical hE hMZL
      hO4 with ⟨s₁, -, m, f₁, hm, hf₁, hSp₁, t, ht, hO⟩ | ⟨k, ε, π, hk, h5, -⟩ |
      ⟨f₂, n₂, -, hn₂, ⟨e⟩, -⟩
  · rcases (show n - 2 = 2 ∨ 3 ≤ n - 2 by omega) with h2 | h3
    · have hU2 : IsUnitaryTransvection _ 2 f s' := h2 ▸ hU'
      have hSp' := isSymplecticTransvection_of_isUnitaryTransvection_two hU2
      obtain ⟨rfl, rfl⟩ := isSymplecticTransvection_rigid hf₁ hf hm (le_refl 2) hSp₁ hSp'
      exact ⟨by omega, t, ht, hO⟩
    · exact absurd hSp₁ (not_isSymplecticTransvection_of_isUnitaryTransvection h3 hf hf₁ hm hU')
  · exact absurd h5 (not_isFiveReflectionModel_of_isUnitaryTransvection hcls hZL hs' hf hU' hk)
  · exact absurd ⟨e⟩
      (not_nonempty_mulEquiv_l2Wreath_of_isUnitaryTransvection hZL (by omega) hf hU' (by omega))

theorem eq_four_and_isOrthReflection_closure_of_pivot_u (hIH : Theorem4Below (Nat.card G))
    (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y)
    {Ω : Set G} (hΩ : Ω ⊆ commSet D x ∩ commSet D y) (hdΩ : hC.d ∈ Ω)
    (hΔΩ : commSet D x ∩ commSet D y ∩ commSet D hC.d ⊆ Ω)
    (hcls : ∃ t : Subgroup.closure Ω, inClosure Ω = {g | IsConj t g})
    (hconn : ¬ CFSG.Timmesfeld.Connectivity.Disconnected (inClosure Ω))
    (hcen : CFSG.solvableRadical (Subgroup.closure Ω) ≤ Subgroup.center (Subgroup.closure Ω)) :
    n = 4 ∧ ∃ t, ∃ ht : t ∈ Ω,
      IsOrthReflection (Subgroup.closure Ω) 4 f ⟨t, Subgroup.subset_closure ht⟩ := by
  have hΩD : Ω ⊆ D := fun z hz => (hΩ hz).1.1
  have hS := setup_inClosure hC.setup.oddT hΩD hcls
  have hns := not_isSolvable_closure_of_subset_u hC hMZ hα hs hn hf hU hx hy hxy hΔΩ
  obtain ⟨hCL, hd⟩ := exists_hypothesisC_inClosure hC.setup.oddT hΩD hdΩ hcls hconn hns
  obtain ⟨h4, _, ⟨t, ht, rfl⟩, hO⟩ := eq_four_and_exists_isOrthReflection_barSet_u hIH hC hMZ hα hs
    hn hf hU hx hy hxy hΩ hdΩ hΔΩ hcen hS hns hCL hd
  exact ⟨h4, (t : G), ht, isOrthReflection_of_quotient_solvableRadical hcen hO⟩

end PivotG4

section Component

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_rootTwin_commSet_u (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {b : G} (hb : b ∈ commSet D hC.d) :
    ∃ c ∈ commSet D hC.d, c ≠ b ∧ ∀ e ∈ commSet D hC.d, Commute e c ↔ Commute e b := by
  classical
  have hZ := center_Hbar_eq_bot hC
  have hbE : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (⟨b, mem_Halpha_of_mem_commSet hC hα hb⟩ : Halpha D hC.alpha) ∈ imageClass hC :=
    ⟨_, mem_DstarH_of_mem_commSet hC hα hb, rfl⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_mem_imageClass hC hs hbE)
  have hUb := isUnitaryTransvection_map (MulAut.conj g) hU
  rw [MulAut.conj_apply, hg] at hUb
  have hcard := ncard_rootBlock_of_isUnitaryTransvection (imageClass_isClass hC) hZ hbE hn hUb
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hnt : (rootBlock (imageClass hC) (QuotientGroup.mk' _
      (⟨b, mem_Halpha_of_mem_commSet hC hα hb⟩ : Halpha D hC.alpha))).Nontrivial := by
    rw [← Set.one_lt_ncard_iff_nontrivial, hcard]
    omega
  obtain ⟨_, hcbar, hcbarb⟩ := hnt.exists_ne (QuotientGroup.mk' _
    (⟨b, mem_Halpha_of_mem_commSet hC hα hb⟩ : Halpha D hC.alpha))
  obtain ⟨cH, hcH, rfl⟩ := hcbar.1
  have hcd : (cH : G) ∈ commSet D hC.d := by
    rw [← Nine.DalphaStar_eq_commSet hC hα]
    exact (mem_DstarH_iff hC).mp hcH
  refine ⟨cH, hcd, fun h => hcbarb ?_, fun e he => ?_⟩
  · congr 1
    exact Subtype.ext h
  · rw [commute_iff_commute_mk hC hMZ hα he hcd, commute_iff_commute_mk hC hMZ hα he hb]
    exact hcbar.2 _ ⟨_, mem_DstarH_of_mem_commSet hC hα he, rfl⟩

theorem localPivot_pivot_u (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    LocalPivot D x y hC.d := by
  classical
  have htwin : ∀ b ∈ gammaAt D x y hC.d, ∃ c ∈ gammaAt D x y hC.d, c ≠ b ∧ Commute c b ∧
      ∀ e ∈ gammaAt D x y hC.d, Commute e c ↔ Commute e b := by
    intro b hb
    obtain ⟨c, hc, hcb, hiff⟩ := exists_rootTwin_commSet_u hC hMZ hα hs hn hf hU hb.2
    have hcx : Commute x c := (hiff x hx).mpr hb.1.1.2.1.symm
    have hcy : Commute y c := (hiff y hy).mpr hb.1.2.2.1.symm
    refine ⟨c, ⟨⟨⟨hc.1, hcx.symm, ?_⟩, ⟨hc.1, hcy.symm, ?_⟩⟩, hc⟩, hcb,
      ((hiff b hb.2).mpr (Commute.refl b)).symm, fun e he => hiff e he.2⟩
    · rintro rfl
      exact hxy hcy.symm
    · rintro rfl
      exact hxy hcx
  have hZ := center_Hbar_eq_bot hC
  obtain ⟨t, ht, hts, htu, htw, -, hcl⟩ := isUnitaryTransvection_closure_commonCommute hZ hn
    (ne_five_one_of_two_le hf) hU
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hx, rfl⟩)
    (isConj_of_mem_imageClass hC hs ⟨_, mem_DstarH_of_mem_commSet hC hα hy, rfl⟩)
    (not_commute_mk_of_mem_commSet hC hMZ hα hx hy hxy)
  have hne := (subset_rootBlock_and_ne_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs
    hn hU).2
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs hne
  have himg := image_commonPerpH hC hMZ hα hs hx hy hxy
  have hmem : ∀ b (hb : b ∈ gammaAt D x y hC.d),
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (⟨b, mem_Halpha_of_mem_commSet hC hα hb.2⟩ : Halpha D hC.alpha) ∈ {z | IsConj s z ∧
          Commute z (QuotientGroup.mk' _ ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩) ∧
          Commute z (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩)} := by
    intro b hb
    have h1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (⟨b, mem_Halpha_of_mem_commSet hC hα hb.2⟩ : Halpha D hC.alpha) ∈
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) '' commonPerpH hC x y :=
      ⟨_, hb, rfl⟩
    rw [himg] at h1
    exact h1
  refine ⟨?_, fun b hb b' hb' => ?_, fun b hb => ?_, fun b hb => ?_, ?_⟩
  · have h1 : t ∈ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ''
        commonPerpH hC x y := by
      rw [himg]
      exact ⟨hts, htu, htw⟩
    obtain ⟨w, hw, -⟩ := h1
    exact ⟨(w : G), hw⟩
  · obtain ⟨g, -, hg⟩ := exists_conj_deltaIn_u hC hMZ hα hs hn hf hU hx hy hxy
      (Ω := gammaAt D x y hC.d) subset_rfl (δ := ⟨b, Subgroup.subset_closure hb⟩)
      (δ' := ⟨b', Subgroup.subset_closure hb'⟩) hb hb'
    exact ⟨g, g.2, congrArg Subtype.val hg⟩
  · obtain ⟨c, hc, hcb, hcomm, -⟩ := htwin b hb
    exact ⟨c, hc, hcb, hcomm⟩
  · by_contra h
    push Not at h
    obtain ⟨c, hc, hcb, -, -⟩ := htwin b hb
    apply hcb
    set Δb := {z | IsConj s z ∧
      Commute z (QuotientGroup.mk' _ ⟨x, mem_Halpha_of_mem_commSet hC hα hx⟩) ∧
      Commute z (QuotientGroup.mk' _ ⟨y, mem_Halpha_of_mem_commSet hC hα hy⟩)} with hΔb
    set bb := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (⟨b, mem_Halpha_of_mem_commSet hC hα hb.2⟩ : Halpha D hC.alpha) with hbb
    have hcen : Subgroup.closure Δb ≤ Subgroup.centralizer {bb} := by
      rw [Subgroup.closure_le]
      intro z hz
      have hz' : z ∈ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ''
          commonPerpH hC x y := by
        rw [himg]
        exact hz
      obtain ⟨w, hw, rfl⟩ := hz'
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h1 : Commute (w : G) b := (h (w : G) hw).symm
      exact ((commute_iff_commute_mk hC hMZ hα hw.2 hb.2).mp h1).eq
    obtain ⟨g₁, hg₁, he₁⟩ := (hcl _).mp (hmem c hc)
    obtain ⟨g₂, hg₂, he₂⟩ := (hcl _).mp (hmem b hb)
    have hceq : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (⟨c, mem_Halpha_of_mem_commSet hC hα hc.2⟩ : Halpha D hC.alpha) = bb := by
      rw [← he₁]
      have ht2 : t = g₂⁻¹ * bb * g₂ := by rw [hbb, ← he₂]; group
      have hgc := Subgroup.mem_centralizer_singleton_iff.mp
        (hcen (Subgroup.mul_mem _ hg₁ (Subgroup.inv_mem _ hg₂)))
      rw [ht2]
      calc g₁ * (g₂⁻¹ * bb * g₂) * g₁⁻¹ = (g₁ * g₂⁻¹) * bb * (g₁ * g₂⁻¹)⁻¹ := by group
        _ = bb * (g₁ * g₂⁻¹) * (g₁ * g₂⁻¹)⁻¹ := by rw [hgc]
        _ = bb := by group
    exact congrArg Subtype.val (hinj (mem_DstarH_of_mem_commSet hC hα hc.2)
      (mem_DstarH_of_mem_commSet hC hα hb.2) hceq)
  · intro b hb b' hb' htw
    by_contra hne'
    by_cases hc : Commute b' b
    · exact ((htw b' hb').mp ⟨fun h => hne' h.symm, hc⟩).1 rfl
    · obtain ⟨c, hcΔ, hcb, hcomm, hiff⟩ := htwin b hb
      have h1 : Commute c b' := ((htw c hcΔ).mp ⟨hcb, hcomm⟩).2
      exact hc ((hiff b' hb').mp h1.symm)

theorem localPivot_of_mem_u (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {v x y : G} (hv : v ∈ D) (hx : x ∈ commSet D v) (hy : y ∈ commSet D v)
    (hxy : ¬ Commute x y) : LocalPivot D x y v := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hv)
  set φ := MulAut.conj g with hφdef
  have hφD : ∀ z, φ z ∈ D ↔ z ∈ D := by
    intro z
    rw [MulAut.conj_apply]
    refine ⟨fun h => ?_, fun h => hC.setup.conj_mem g h⟩
    have := hC.setup.conj_mem g⁻¹ h
    simpa [mul_assoc] using this
  have hd : g * hC.d * g⁻¹ = φ hC.d := (MulAut.conj_apply g hC.d).symm
  have hx' : φ.symm x ∈ commSet D hC.d := by
    rw [← mem_commSet_map_iff φ hφD, MulEquiv.apply_symm_apply, ← hd]
    exact hx
  have hy' : φ.symm y ∈ commSet D hC.d := by
    rw [← mem_commSet_map_iff φ hφD, MulEquiv.apply_symm_apply, ← hd]
    exact hy
  have hxy' : ¬ Commute (φ.symm x) (φ.symm y) := fun h =>
    hxy (by simpa using (commute_map_iff φ).mpr h)
  have h := (localPivot_pivot_u hC hMZ hα hs hn hf hU hx' hy' hxy').map φ hφD
  rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← hd] at h

theorem twelveSix_u_component (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    n = 4 ∧ ∃ t, ∃ ht : t ∈ compSet D x y hC.d,
      IsOrthReflection (Subgroup.closure (compSet D x y hC.d)) 4 f
        ⟨t, Subgroup.subset_closure ht⟩ := by
  have hdΓ := d_mem_commSet_inter hC hx hy
  have hN := hC.setup.normal
  have hD := hC.setup.oddT
  have hloc : ∀ v ∈ compSet D x y hC.d, LocalPivot D x y v := fun v hv =>
    localPivot_of_mem_u hC hMZ hα hs hn hf hU hv.1.1.1
      ⟨hx.1, hv.1.1.2.1.symm, fun h => hv.1.1.2.2 h.symm⟩
      ⟨hy.1, hv.1.2.2.1.symm, fun h => hv.1.2.2.2 h.symm⟩ hxy
  have hcls := isClass_inClosure_compSet hN hD hdΓ (fun v hv => (hloc v hv).2.1)
    (fun v hv => (hloc v hv).2.2.1)
  have hS := setup_inClosure hD (fun z hz => hz.1.1.1) hcls
  have hcen := solvableRadical_le_center_of_noTwins hS
    (noOpenTwins_inClosure_compSet (fun v hv => (hloc v hv).1) fun v hv => (hloc v hv).2.2.2.2)
    (noClosedTwins_inClosure_compSet fun v hv => (hloc v hv).2.2.2.1)
  exact eq_four_and_isOrthReflection_closure_of_pivot_u hIH hC hMZ hα hs hn hf hU hx hy hxy
    (compSet_subset D x y hC.d) (mem_compSet_self hdΓ) (gammaAt_self_subset_compSet hdΓ) hcls
    (not_disconnected_inClosure_compSet hdΓ) hcen

theorem eq_four_of_isUnitaryTransvection (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s) : n = 4 := by
  have hZ := center_Hbar_eq_bot hC
  have hne := (subset_rootBlock_and_ne_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs
    hn hU).2
  obtain ⟨b, hb, hsb⟩ := exists_not_commute_of_rootBlock_ne (imageClass_isClass hC) hs hne s hs
  obtain ⟨xH, hxH, rfl⟩ := hs
  obtain ⟨yH, hyH, rfl⟩ := hb
  have hx : (xH : G) ∈ commSet D hC.d := by
    rw [← Nine.DalphaStar_eq_commSet hC hα]
    exact (mem_DstarH_iff hC).mp hxH
  have hy : (yH : G) ∈ commSet D hC.d := by
    rw [← Nine.DalphaStar_eq_commSet hC hα]
    exact (mem_DstarH_iff hC).mp hyH
  have hxy : ¬ Commute (xH : G) (yH : G) := fun h =>
    hsb ((commute_iff_commute_mk hC hMZ hα hx hy).mp h)
  exact (twelveSix_u_component hIH hC hMZ hα ⟨xH, hxH, rfl⟩ hn hf hU hx hy hxy).1

end Component

end CFSG.OddTranspositions.PartThree

end
