module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmFour
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmHyp
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightLeviBasic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.Quasithin.Background.SzG11G94Solv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL

public section

namespace CFSG.StandardType.KGOm

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal.Spin (HypFrame)
open CFSG.StandardType.RCSTOm
open scoped MatrixGroups

theorem centralizer_decomp_frame_four {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) (F : HypFrame Q 4)
    (hF0 : ∀ x : V, (∀ k u, polar Q (F.vec k u) x = 0) → x = 0) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (s t : Bool) {c : K} (hc : c ≠ 0) (hK : 4 ≤ Nat.card K)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
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
        (rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ ∧
      (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ =
        (leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true)).comap σ ⊔
          (leviFix (elementaryGroup Q) (framePair F k true)
            (flipPair (framePair F l true))).comap σ := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite U := Finite.of_injective σ hσ
  have hEich : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  have h₁₂ := orth₁₂ F hij s t hc
  have h₁₃ := orth₁₃ F hjk t true
  have h₁₄ := orth₁₃ F hjl t true
  have h₂₃ := orth₂₃ F hik s true hc
  have h₂₄ := orth₂₃ F hil s true hc
  have h₃₄ := framePair_orth F hkl true true
  have h₁₄' := orth_flip h₁₄
  have h₂₄' := orth_flip h₂₄
  have h₃₄' := orth_flip h₃₄
  have hspan₁ : ∀ w, InW (framePair F j t) (smulPair (framePair F i s) hc) w →
      w = polar Q w (framePair F k true).f • (framePair F k true).e +
        polar Q w (framePair F k true).e • (framePair F k true).f +
        (polar Q w (framePair F l true).f • (framePair F l true).e +
          polar Q w (framePair F l true).e • (framePair F l true).f) := fun w hw =>
    eq_comb_of_inW_four F hF0 hij hik hil hjk hjl hkl hc hw
  have hspan₂ : ∀ w, InW (framePair F j t) (smulPair (framePair F i s) hc) w →
      w = polar Q w (framePair F k true).f • (framePair F k true).e +
        polar Q w (framePair F k true).e • (framePair F k true).f +
        (polar Q w (flipPair (framePair F l true)).f • (flipPair (framePair F l true)).e +
          polar Q w (flipPair (framePair F l true)).e • (flipPair (framePair F l true)).f) :=
    fun w hw => by
      conv_lhs => rw [hspan₁ w hw]
      simp only [flipPair_e, flipPair_f]
      abel
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  have hWeq : wSub (framePair F j t) (smulPair (framePair F i s) hc) =
      spanU₄ (framePair F k true) (framePair F l true) := by
    apply le_antisymm
    · intro w hw
      rw [hspan₁ w (mem_wSub.mp hw)]
      exact add_mem (add_mem (Submodule.smul_mem _ _ mem_spanU₄_e₁)
        (Submodule.smul_mem _ _ mem_spanU₄_f₁))
        (add_mem (Submodule.smul_mem _ _ mem_spanU₄_e₂) (Submodule.smul_mem _ _ mem_spanU₄_f₂))
    · rw [spanU₄, Submodule.span_le]
      rintro _ (rfl | rfl | rfl | rfl)
      · exact vec_mem_wSub F hik hjk hc true
      · exact vec_mem_wSub F hil hjl hc true
      · exact vec_mem_wSub F hik hjk hc false
      · exact vec_mem_wSub F hil hjl hc false
  have hdim : finrank K (wSub (framePair F j t) (smulPair (framePair F i s) hc)) = 4 := by
    rw [hWeq, finrank_spanU₄ h₃₄]
  have hS := exists_totallySingular_two (R := Q.restrict (wSub (framePair F j t)
      (smulPair (framePair F i s) hc)))
    (orth_restrictPair h₃₄ (vec_mem_wSub F hik hjk hc true) (vec_mem_wSub F hik hjk hc false)
      (vec_mem_wSub F hil hjl hc true) (vec_mem_wSub F hil hjl hc false))
  have hLa := leviFix_le_omFix (Q := Q) h₁₃ h₁₄ h₂₃ h₂₄
  have hLb := leviFix_le_omFix (Q := Q) h₁₃ h₁₄' h₂₃ h₂₄'
  have hab := leviFix_le_centralizer_flip h₃₄ hEich hEich
  have hdisj := leviFix_inf_flip_eq_bot (Q := Q) h₃₄
  have hΩ := omegaGroup_le_orthDerived_of_splitFour hR hdim hS hK
  have hcardR := card_orthDerived_le_four hR hdim hS hK
  have hcardR' : Nat.card (orthDerived (Q.restrict (wSub (framePair F j t)
        (smulPair (framePair F i s) hc)))) ≤
      Nat.card SL(2, K) * Nat.card SL(2, K) := by
    simpa [_root_.sq] using hcardR
  have hcard' : Nat.card (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)) ≤
      Nat.card (leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true)) *
        Nat.card (leviFix (elementaryGroup Q) (framePair F k true)
          (flipPair (framePair F l true))) := by
    rw [Nat.card_congr (omFixEquiv h₁₂ hQ hEΩ hOE hR hΩ).toEquiv,
      Nat.card_congr (leviFixEquiv _ _ h₃₄ hEich).toEquiv,
      Nat.card_congr (leviFixEquiv _ _ h₃₄' hEich).toEquiv]
    exact hcardR'
  have hgenV : omFix Q (framePair F j t) (smulPair (framePair F i s) hc) =
      leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true) ⊔
        leviFix (elementaryGroup Q) (framePair F k true) (flipPair (framePair F l true)) := by
    refine le_antisymm (fun g hg => ?_) (sup_le hLa hLb)
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_card_le hLa hLb hab hdisj hcard' g hg
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  have hRE : rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc) ≤ σ.range :=
    hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) (framePair F j t) (smulPair (framePair F i s) hc) ≤
      σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q (framePair F j t) (smulPair (framePair F i s) hc) ≤ σ.range :=
    hσE ▸ fun g hg => (mem_omFix.mp hg).1
  have hLaE : leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true) ≤
      σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hLbE : leviFix (elementaryGroup Q) (framePair F k true)
      (flipPair (framePair F l true)) ≤ σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  set R : Subgroup U :=
    (rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ with hRdef
  set L₁ : Subgroup U :=
    (leviFix (elementaryGroup Q) (framePair F j t)
      (smulPair (framePair F i s) hc)).comap σ with hL₁def
  set L₂ : Subgroup U :=
    (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ with hL₂def
  set B₁ : Subgroup U :=
    (leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true)).comap σ with hB₁def
  set B₂ : Subgroup U :=
    (leviFix (elementaryGroup Q) (framePair F k true)
      (flipPair (framePair F l true))).comap σ with hB₂def
  have hx' : σ x = eichler Q (framePair F j t).e (smulPair (framePair F i s) hc).e := hx
  have hC : Subgroup.centralizer ({x} : Set U) = R ⊔ (L₁ ⊔ L₂) := by
    rw [centralizer_eq_comap hσ hσE x, hx', centralizer_inf_elementaryGroup_eq h₁₂,
      comap_sup_of_le_range hσ (sup_le hRE hL₁E) hL₂E,
      comap_sup_of_le_range hσ hRE hL₁E, hRdef, hL₁def, hL₂def]
    simp only [sup_assoc]
  have hnorm : (leviFix (elementaryGroup Q) (framePair F j t)
        (smulPair (framePair F i s) hc)).comap σ ⊔
        (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ ≤
      Subgroup.normalizer
        ((rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ : Set U) :=
    sup_le (comap_le_normalizer (leviFix_le_normalizer_rootRadical h₁₂))
      (comap_le_normalizer (omFix_le_normalizer_rootRadical h₁₂))
  have hdisjC : Disjoint ((rootRadical Q (framePair F j t)
        (smulPair (framePair F i s) hc)).comap σ)
      ((leviFix (elementaryGroup Q) (framePair F j t)
          (smulPair (framePair F i s) hc)).comap σ ⊔
        (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ) := by
    rw [Subgroup.disjoint_def]
    intro y hy hy'
    have hσy : σ y ∈ leviFix (elementaryGroup Q) (framePair F j t)
        (smulPair (framePair F i s) hc) ⊔
        omFix Q (framePair F j t) (smulPair (framePair F i s) hc) := by
      have h := hy'
      rwa [show (leviFix (elementaryGroup Q) (framePair F j t)
            (smulPair (framePair F i s) hc)).comap σ ⊔
            (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ =
          (leviFix (elementaryGroup Q) (framePair F j t)
            (smulPair (framePair F i s) hc) ⊔
            omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ from
          (comap_sup_of_le_range hσ hL₁E hL₂E).symm, Subgroup.mem_comap] at h
    exact hσ (by
      rw [Subgroup.disjoint_def.mp (disjoint_rootRadical_sup h₁₂)
        (Subgroup.mem_comap.mp hy) hσy, map_one])
  have hgenU : L₂ = B₁ ⊔ B₂ := by
    rw [hL₂def, hB₁def, hB₂def, hgenV, comap_sup_of_le_range hσ hLaE hLbE]
  have hR2 : IsPGroup 2 R := IsPGroup.comap_of_injective isPGroup_rootRadical σ hσ
  have h1Q : L₁ ≤ Subgroup.normalizer (R : Set U) :=
    comap_le_normalizer (leviFix_le_normalizer_rootRadical h₁₂)
  have h2Q : L₂ ≤ Subgroup.normalizer (R : Set U) :=
    comap_le_normalizer (omFix_le_normalizer_rootRadical h₁₂)
  have hB₁Q : B₁ ≤ Subgroup.normalizer (R : Set U) := (Subgroup.comap_mono hLa).trans h2Q
  have hB₂Q : B₂ ≤ Subgroup.normalizer (R : Set U) := (Subgroup.comap_mono hLb).trans h2Q
  have hcomapCentral : ∀ {A B C : Subgroup (V ≃ₗ[K] V)},
      A ≤ Subgroup.centralizer (C : Set (V ≃ₗ[K] V)) → B ≤ C →
      A.comap σ ≤ Subgroup.centralizer ((B.comap σ : Subgroup U) : Set U) := by
    intro A B C hAC hBC g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    apply hσ
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp (hAC (Subgroup.mem_comap.mp hg)) (σ h)
      (hBC (Subgroup.mem_comap.mp hh))
  have hAB₁ : L₁ ≤ Subgroup.centralizer (B₁ : Set U) :=
    hcomapCentral (leviFix_le_centralizer_omFix h₁₂) hLa
  have hAB₂ : L₁ ≤ Subgroup.centralizer (B₂ : Set U) :=
    hcomapCentral (leviFix_le_centralizer_omFix h₁₂) hLb
  have hB₁B₂ : B₁ ≤ Subgroup.centralizer (B₂ : Set U) :=
    hcomapCentral hab le_rfl
  have hSL : CFSG.IsQuasisimple (SL(2, K)) :=
    CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK)
  have eA : ↥L₁ ≃* SL(2, K) :=
    (L₁.equivMapOfInjective σ hσ).trans
      ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL₁E)).trans
        (leviFixEquiv (framePair F j t) (smulPair (framePair F i s) hc) h₁₂ hEich))
  have eB₁ : ↥B₁ ≃* SL(2, K) :=
    (B₁.equivMapOfInjective σ hσ).trans
      ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLaE)).trans
        (leviFixEquiv (framePair F k true) (framePair F l true) h₃₄ hEich))
  have eB₂ : ↥B₂ ≃* SL(2, K) :=
    (B₂.equivMapOfInjective σ hσ).trans
      ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLbE)).trans
        (leviFixEquiv (framePair F k true) (flipPair (framePair F l true)) h₃₄' hEich))
  have qz : ∀ L : Subgroup U, (↥L ≃* SL(2, K)) →
      CFSG.IsQuasisimple L ∧ Subgroup.center L = ⊥ :=
    fun L e => ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSL, by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e.symm,
        center_SL2_eq_bot_of_charTwo, Subgroup.map_bot]⟩
  obtain ⟨hAq, hAZ⟩ := qz L₁ eA
  obtain ⟨hB₁q, hB₁Z⟩ := qz B₁ eB₁
  obtain ⟨hB₂q, hB₂Z⟩ := qz B₂ eB₂
  have hX : Subgroup.centralizer ({x} : Set U) = R ⊔ (L₁ ⊔ B₁ ⊔ B₂) := by
    rw [hC, hgenU]
    ac_rfl
  have hO2 : pCoreOf 2 (Subgroup.centralizer {x}) = R :=
    pCoreOf_eq_of_three_summands hX hR2 h1Q hB₁Q hB₂Q hAB₁ hAB₂ hB₁B₂
      (ggRCSOmSummand_of_isQuasisimple hAq hAZ)
      (ggRCSOmSummand_of_isQuasisimple hB₁q hB₁Z)
      (ggRCSOmSummand_of_isQuasisimple hB₂q hB₂Z)
  exact ⟨hC, hnorm, hdisjC, hO2, hgenU⟩

theorem isSolvable_centralizer_frame_four_two {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (F : HypFrame Q 4)
    (hF0 : ∀ x : V, (∀ k u, polar Q (F.vec k u) x = 0) → x = 0) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (s t : Bool) {c : K} (hc : c ≠ 0) (hK : Nat.card K = 2)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U}
    (hx : σ x = eichler Q (F.vec j t) (c • F.vec i s)) :
    Group.IsSolvable (Subgroup.centralizer ({x} : Set U)) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite U := Finite.of_injective σ hσ
  have hEich : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  have h₁₂ := orth₁₂ F hij s t hc
  have h₁₃ := orth₁₃ F hjk t true
  have h₁₄ := orth₁₃ F hjl t true
  have h₂₃ := orth₂₃ F hik s true hc
  have h₂₄ := orth₂₃ F hil s true hc
  have h₃₄ := framePair_orth F hkl true true
  have hspan₁ : ∀ w, InW (framePair F j t) (smulPair (framePair F i s) hc) w →
      w = polar Q w (framePair F k true).f • (framePair F k true).e +
        polar Q w (framePair F k true).e • (framePair F k true).f +
        (polar Q w (framePair F l true).f • (framePair F l true).e +
          polar Q w (framePair F l true).e • (framePair F l true).f) := fun w hw =>
    eq_comb_of_inW_four F hF0 hij hik hil hjk hjl hkl hc hw
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  have hWeq : wSub (framePair F j t) (smulPair (framePair F i s) hc) =
      spanU₄ (framePair F k true) (framePair F l true) := by
    apply le_antisymm
    · intro w hw
      rw [hspan₁ w (mem_wSub.mp hw)]
      exact add_mem (add_mem (Submodule.smul_mem _ _ mem_spanU₄_e₁)
        (Submodule.smul_mem _ _ mem_spanU₄_f₁))
        (add_mem (Submodule.smul_mem _ _ mem_spanU₄_e₂) (Submodule.smul_mem _ _ mem_spanU₄_f₂))
    · rw [spanU₄, Submodule.span_le]
      rintro _ (rfl | rfl | rfl | rfl)
      · exact vec_mem_wSub F hik hjk hc true
      · exact vec_mem_wSub F hil hjl hc true
      · exact vec_mem_wSub F hik hjk hc false
      · exact vec_mem_wSub F hil hjl hc false
  have hdim : finrank K (wSub (framePair F j t) (smulPair (framePair F i s) hc)) = 4 := by
    rw [hWeq, finrank_spanU₄ h₃₄]
  have hS := exists_totallySingular_two (R := Q.restrict (wSub (framePair F j t)
      (smulPair (framePair F i s) hc)))
    (orth_restrictPair h₃₄ (vec_mem_wSub F hik hjk hc true) (vec_mem_wSub F hik hjk hc false)
      (vec_mem_wSub F hil hjl hc true) (vec_mem_wSub F hil hjl hc false))
  have hRE : rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc) ≤ σ.range :=
    hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) (framePair F j t) (smulPair (framePair F i s) hc) ≤
      σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q (framePair F j t) (smulPair (framePair F i s) hc) ≤ σ.range :=
    hσE ▸ fun g hg => (mem_omFix.mp hg).1
  set R : Subgroup U :=
    (rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ with hRdef
  set L₁ : Subgroup U :=
    (leviFix (elementaryGroup Q) (framePair F j t)
      (smulPair (framePair F i s) hc)).comap σ with hL₁def
  set L₂ : Subgroup U :=
    (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ with hL₂def
  have hx' : σ x = eichler Q (framePair F j t).e (smulPair (framePair F i s) hc).e := hx
  have hC : Subgroup.centralizer ({x} : Set U) = R ⊔ (L₁ ⊔ L₂) := by
    rw [centralizer_eq_comap hσ hσE x, hx', centralizer_inf_elementaryGroup_eq h₁₂,
      comap_sup_of_le_range hσ (sup_le hRE hL₁E) hL₂E,
      comap_sup_of_le_range hσ hRE hL₁E, hRdef, hL₁def, hL₂def]
    simp only [sup_assoc]
  have hnorm : L₁ ⊔ L₂ ≤ Subgroup.normalizer (R : Set U) :=
    sup_le (comap_le_normalizer (leviFix_le_normalizer_rootRadical h₁₂))
      (comap_le_normalizer (omFix_le_normalizer_rootRadical h₁₂))
  have hdisjC : Disjoint R (L₁ ⊔ L₂) := by
    rw [Subgroup.disjoint_def]
    intro y hy hy'
    have hσy : σ y ∈ leviFix (elementaryGroup Q) (framePair F j t)
        (smulPair (framePair F i s) hc) ⊔
        omFix Q (framePair F j t) (smulPair (framePair F i s) hc) := by
      have h := hy'
      rwa [show L₁ ⊔ L₂ = (leviFix (elementaryGroup Q) (framePair F j t)
            (smulPair (framePair F i s) hc) ⊔
            omFix Q (framePair F j t) (smulPair (framePair F i s) hc)).comap σ from
          (comap_sup_of_le_range hσ hL₁E hL₂E).symm, Subgroup.mem_comap] at h
    exact hσ (by
      rw [Subgroup.disjoint_def.mp (disjoint_rootRadical_sup h₁₂)
        (Subgroup.mem_comap.mp hy) hσy, map_one])
  have h21V : omFix Q (framePair F j t) (smulPair (framePair F i s) hc) ≤
      Subgroup.normalizer (leviFix (elementaryGroup Q) (framePair F j t)
        (smulPair (framePair F i s) hc) : Set (V ≃ₗ[K] V)) :=
    (Subgroup.le_centralizer_iff.mp (leviFix_le_centralizer_omFix h₁₂)).trans
      (Subgroup.centralizer_le_normalizer _)
  have h12norm : L₂ ≤ Subgroup.normalizer (L₁ : Set U) := comap_le_normalizer h21V
  have hdisj12 : Disjoint L₁ L₂ := by
    rw [Subgroup.disjoint_def]
    intro y hy hy'
    exact hσ (by
      rw [Subgroup.disjoint_def.mp (disjoint_leviFix_omFix h₁₂)
        (Subgroup.mem_comap.mp hy) (Subgroup.mem_comap.mp hy'), map_one])
  have hcardC : Nat.card (Subgroup.centralizer ({x} : Set U)) =
      Nat.card R * (Nat.card L₁ * Nat.card L₂) := by
    rw [hC, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer R (L₁ ⊔ L₂)
      hnorm hdisjC,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer L₁ L₂ h12norm hdisj12]
  have hR2 : IsPGroup 2 R := IsPGroup.comap_of_injective isPGroup_rootRadical σ hσ
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR2
  have eA : ↥L₁ ≃* SL(2, K) :=
    (L₁.equivMapOfInjective σ hσ).trans
      ((MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL₁E)).trans
        (leviFixEquiv (framePair F j t) (smulPair (framePair F i s) hc) h₁₂ hEich))
  obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
  have hL₁card : Nat.card L₁ = 6 := by
    rw [Nat.card_congr (eA.trans e3).toEquiv, card_perm_three]
  have eL₂ : ↥L₂ ≃* omFix Q (framePair F j t) (smulPair (framePair F i s) hc) :=
    (L₂.equivMapOfInjective σ hσ).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL₂E))
  have hL₂dvd : Nat.card L₂ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (Q.restrict (wSub (framePair F j t) (smulPair (framePair F i s) hc)))) := by
    rw [Nat.card_congr eL₂.toEquiv,
      Nat.card_congr (MonoidHom.ofInjective (resW_injective (Q := Q) h₁₂)).toEquiv]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨g, rfl⟩
    exact resW_mem_orthogonalGroup g
  have hprime : ∀ r : ℕ, r.Prime →
      r ∣ Nat.card (Subgroup.centralizer ({x} : Set U)) → r = 2 ∨ r = 3 := by
    intro r hr hrd
    rw [hcardC, hn, hL₁card] at hrd
    rcases hr.dvd_mul.mp hrd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
    · rcases hr.dvd_mul.mp h with h6 | hB
      · have h23 : r ∣ 2 * 3 := by simpa using h6
        rcases hr.dvd_mul.mp h23 with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
      · exact eq_two_or_three_of_dvd_card_four hR hdim hS hK hr (dvd_trans hB hL₂dvd)
  exact CFSG.Quasithin.SzG11G94.isSolvable_of_prime_divisors hprime

end CFSG.StandardType.KGOm

end
