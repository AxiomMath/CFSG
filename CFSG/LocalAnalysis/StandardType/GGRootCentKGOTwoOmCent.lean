module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmHyp
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmMinus
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL

public section

namespace CFSG.StandardType.KGOm

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.StandardType.RCSTOm
open scoped MatrixGroups commutatorElement

theorem centralizer_decomp_frame {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (h₁₂ : P₁.Orth P₂)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂)) (RCSTOm.nondegenerate_restrict_wSub hQ h₁₂) ≤
      orthDerived (Q.restrict (wSub P₁ P₂)))
    (hWq : CFSG.IsQuasisimple (orthDerived (Q.restrict (wSub P₁ P₂))))
    (hWZ : Subgroup.center (orthDerived (Q.restrict (wSub P₁ P₂))) = ⊥)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e) :
    Subgroup.centralizer {x} = (rootRadical Q P₁ P₂).comap σ ⊔
        ((leviFix (elementaryGroup Q) P₁ P₂).comap σ ⊔ (omFix Q P₁ P₂).comap σ) ∧
      (leviFix (elementaryGroup Q) P₁ P₂).comap σ ⊔ (omFix Q P₁ P₂).comap σ ≤
        Subgroup.normalizer ((rootRadical Q P₁ P₂).comap σ : Set U) ∧
      Disjoint ((rootRadical Q P₁ P₂).comap σ)
        ((leviFix (elementaryGroup Q) P₁ P₂).comap σ ⊔ (omFix Q P₁ P₂).comap σ) ∧
      pCoreOf 2 (Subgroup.centralizer {x}) = (rootRadical Q P₁ P₂).comap σ := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite U := Finite.of_injective σ hσ
  have hEich : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  have hRE : rootRadical Q P₁ P₂ ≤ σ.range := hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q P₁ P₂ ≤ σ.range := hσE ▸ fun g hg => (mem_omFix.mp hg).1
  set R : Subgroup U := (rootRadical Q P₁ P₂).comap σ with hRdef
  set L₁ : Subgroup U := (leviFix (elementaryGroup Q) P₁ P₂).comap σ with hL₁def
  set L₂ : Subgroup U := (omFix Q P₁ P₂).comap σ with hL₂def
  have hC : Subgroup.centralizer ({x} : Set U) = R ⊔ (L₁ ⊔ L₂) := by
    rw [centralizer_eq_comap hσ hσE x, hx, centralizer_inf_elementaryGroup_eq h₁₂,
      comap_sup_of_le_range hσ (sup_le hRE hL₁E) hL₂E,
      comap_sup_of_le_range hσ hRE hL₁E, hRdef, hL₁def, hL₂def]
    simp only [sup_assoc]
  rw [hRdef, hL₁def, hL₂def] at hC
  refine ⟨hC, ?_, ?_, ?_⟩
  ·
    rw [hRdef, hL₁def, hL₂def]
    exact sup_le (comap_le_normalizer (leviFix_le_normalizer_rootRadical h₁₂))
      (comap_le_normalizer (omFix_le_normalizer_rootRadical h₁₂))
  ·
    rw [hRdef, hL₁def, hL₂def, Subgroup.disjoint_def]
    intro y hy hy'
    have hσy : σ y ∈ leviFix (elementaryGroup Q) P₁ P₂ ⊔ omFix Q P₁ P₂ := by
      have h := hy'
      rwa [show (leviFix (elementaryGroup Q) P₁ P₂).comap σ ⊔
          (omFix Q P₁ P₂).comap σ = (leviFix (elementaryGroup Q) P₁ P₂ ⊔
            omFix Q P₁ P₂).comap σ from (comap_sup_of_le_range hσ hL₁E hL₂E).symm,
        Subgroup.mem_comap] at h
    exact hσ (by
      rw [Subgroup.disjoint_def.mp (disjoint_rootRadical_sup h₁₂)
        (Subgroup.mem_comap.mp hy) hσy, map_one])
  ·
    have hR2 : IsPGroup 2 ((rootRadical Q P₁ P₂).comap σ) :=
      IsPGroup.comap_of_injective isPGroup_rootRadical σ hσ
    have h1Q : (leviFix (elementaryGroup Q) P₁ P₂).comap σ ≤
        Subgroup.normalizer (((rootRadical Q P₁ P₂).comap σ) : Set U) :=
      comap_le_normalizer (leviFix_le_normalizer_rootRadical h₁₂)
    have h2Q : (omFix Q P₁ P₂).comap σ ≤
        Subgroup.normalizer (((rootRadical Q P₁ P₂).comap σ) : Set U) :=
      comap_le_normalizer (omFix_le_normalizer_rootRadical h₁₂)
    have h12 : (leviFix (elementaryGroup Q) P₁ P₂).comap σ ≤
        Subgroup.centralizer (((omFix Q P₁ P₂).comap σ) : Set U) := by
      intro g hg
      rw [mem_centralizer_iff]
      intro h hh
      apply hσ
      rw [map_mul, map_mul]
      exact mem_centralizer_iff.mp (leviFix_le_centralizer_omFix h₁₂ hg) (σ h) hh
    have eA : ↥((leviFix (elementaryGroup Q) P₁ P₂).comap σ) ≃* SL(2, K) :=
      (((leviFix (elementaryGroup Q) P₁ P₂).comap σ).equivMapOfInjective σ hσ).trans
        ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL₁E)).trans
          (leviFixEquiv P₁ P₂ h₁₂ hEich))
    have hS₁ : GGRCSOmSummand ((leviFix (elementaryGroup Q) P₁ P₂).comap σ) := by
      rcases card_eq_two_or_four_le K with hK | hK
      ·
        obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
        exact ggRCSOmSummand_of_perm (eA.trans e3)
      ·
        have hAq : CFSG.IsQuasisimple ↥((leviFix (elementaryGroup Q) P₁ P₂).comap σ) :=
          CFSG.LocalCores.isQuasisimple_of_mulEquiv eA.symm
            (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl
              (Or.inr hK))
        have hAZ : Subgroup.center ↥((leviFix (elementaryGroup Q) P₁ P₂).comap σ) = ⊥ := by
          rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eA.symm,
            center_SL2_eq_bot_of_charTwo, Subgroup.map_bot]
        exact ggRCSOmSummand_of_isQuasisimple hAq hAZ
    have eB : ↥((omFix Q P₁ P₂).comap σ) ≃*
        ↥(orthDerived (Q.restrict (wSub P₁ P₂))) :=
      (((omFix Q P₁ P₂).comap σ).equivMapOfInjective σ hσ).trans
        ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL₂E)).trans
          (omFixEquiv h₁₂ hQ hEΩ hOE (RCSTOm.nondegenerate_restrict_wSub hQ h₁₂) hΩ))
    have hBq : CFSG.IsQuasisimple ↥((omFix Q P₁ P₂).comap σ) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eB.symm hWq
    have hBZ : Subgroup.center ↥((omFix Q P₁ P₂).comap σ) = ⊥ := by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eB.symm, hWZ,
        Subgroup.map_bot]
    have hS₂ : GGRCSOmSummand ((omFix Q P₁ P₂).comap σ) :=
      ggRCSOmSummand_of_isQuasisimple hBq hBZ
    refine pCoreOf_eq_of_three_summands (L₁ := (leviFix (elementaryGroup Q) P₁ P₂).comap σ)
      (L₂ := (omFix Q P₁ P₂).comap σ) (L₃ := ⊥) ?_ hR2 h1Q h2Q bot_le h12
      (le_centralizer_bot _) (le_centralizer_bot _) hS₁ hS₂ ggRCSOmSummand_bot
    rw [hC, sup_bot_eq]

theorem centralizer_decomp_hypFrame_five {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {N : ℕ}
    (F : HypFrame Q N) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    {i j k l m : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hjk : j ≠ k)
    (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) (s t : Bool) {c : K}
    (hc : c ≠ 0) {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U}
    (hx : σ x = eichler Q (F.vec j t) (c • F.vec i s)) :
    Subgroup.centralizer {x} =
        (rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ ⊔
        ((leviFix (elementaryGroup Q) (framePair F j t)
          (smulPair (framePair F i s) hc)).comap σ ⊔
          (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ) ∧
      (leviFix (elementaryGroup Q) (framePair F j t)
          (smulPair (framePair F i s) hc)).comap σ ⊔
          (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ ≤
        Subgroup.normalizer
          ((rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ : Set U) ∧
      Disjoint ((rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ)
        ((leviFix (elementaryGroup Q) (framePair F j t)
          (smulPair (framePair F i s) hc)).comap σ ⊔
          (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ) ∧
      pCoreOf 2 (Subgroup.centralizer {x}) =
        (rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ := by
  have h₁₂ := orth₁₂ F hij s t hc
  have hR := RCSTOm.nondegenerate_restrict_wSub hQ h₁₂
  have hT := exists_totallySingular_wSub F hik hil him hjk hjl hjm hkl hkm hlm s t hc
  exact centralizer_decomp_frame (P₁ := framePair F j t)
    (P₂ := smulPair (framePair F i s) hc) hQ hEΩ hOE h₁₂
    (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT)
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)
    (center_orthDerived_eq_bot' hR hT (exists_restrict_ne_zero F hik hjk hc))
    hσ hσE hx

end CFSG.StandardType.KGOm

end
