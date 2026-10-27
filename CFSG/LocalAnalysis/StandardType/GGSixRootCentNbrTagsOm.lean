module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNbr
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeNbrTags
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmMinus

public section

namespace CFSG.StandardType

namespace RCSTOm

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal.Spin (HypFrame)

section Frame

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {P₁ P₂ P₃ : HypPair Q}

open scoped MatrixGroups

theorem ggRCSLayerNbr_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) {y₀ : V} (hy₀ : y₀ ≠ 0) (hy₀W : InW P₁ P₂ y₀)
    (hy₀3 : polar Q P₃.e y₀ = 0 ∧ polar Q P₃.f y₀ = 0)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂)) (nondegenerate_restrict_wSub hQ h₁₂) ≤
      orthDerived (Q.restrict (wSub P₁ P₂)))
    (hWq : CFSG.IsQuasisimple (orthDerived (Q.restrict (wSub P₁ P₂))))
    (hWZ : center (orthDerived (Q.restrict (wSub P₁ P₂))) = ⊥)
    (h3 : Nat.card K = 2 → p = 3 → 3 ∣ Nat.card (omFix Q P₁ P₂))
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e)
    (hxC : centralizer {x} ≤ ggOTwoPrime (centralizer {x}))
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) (u : U) :
    GGRCSLayerNbr p ψ.range M (ψ (u * x * u⁻¹)) := by
  have hE : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  set φ := ψ.comp (MulAut.conj u).toMonoidHom with hφdef
  have hφ : Function.Injective φ := RCSTSp.comp_conj_injective hψ u
  have hφr : φ.range = ψ.range := RCSTSp.range_comp_conj ψ u
  have hr : ψ (u * x * u⁻¹) = φ x := by
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr, ← hφr]
  rw [← hφr] at hG₀M hM
  have hRE : rootRadical Q P₁ P₂ ≤ σ.range := hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q P₁ P₂ ≤ σ.range := hσE ▸ fun g hg => (mem_omFix.mp hg).1
  set QG := Φ σ φ (rootRadical Q P₁ P₂) with hQGdef
  set AG := Φ σ φ (leviFix (elementaryGroup Q) P₁ P₂) with hAGdef
  set BG := Φ σ φ (omFix Q P₁ P₂) with hBGdef
  have hX : ggRCSX φ.range (φ x) = QG ⊔ AG ⊔ BG := by
    rw [RCSTSp.ggRCSX_eq_map_centralizer φ hφ hxC, centralizer_eq_comap hσ hσE x, hx,
      centralizer_inf_elementaryGroup_eq h₁₂]
    change Φ σ φ _ = _
    rw [Φ_sup hσ φ (sup_le hRE hL₁E) hL₂E, Φ_sup hσ φ hRE hL₁E]
  have hQ2 : IsPGroup 2 QG := Φ_isPGroup φ hσ isPGroup_rootRadical
  have h1Q : AG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (leviFix_le_normalizer_rootRadical h₁₂)
  have h2Q : BG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (omFix_le_normalizer_rootRadical h₁₂)
  have h12 : AG ≤ centralizer (BG : Set G) :=
    Φ_le_centralizer hσ φ (leviFix_le_centralizer_omFix h₁₂)
  have eA : ↥AG ≃* SL(2, K) := (Φ_equiv hσ φ hφ hL₁E).trans (leviFixEquiv P₁ P₂ h₁₂ hE)
  have eB : ↥BG ≃* ↥(orthDerived (Q.restrict (wSub P₁ P₂))) :=
    (Φ_equiv hσ φ hφ hL₂E).trans
      (omFixEquiv h₁₂ hQ hEΩ hOE (nondegenerate_restrict_wSub hQ h₁₂) hΩ)
  have hBq : CFSG.IsQuasisimple BG := CFSG.LocalCores.isQuasisimple_of_mulEquiv eB.symm hWq
  have hBZ : center BG = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eB.symm, hWZ,
      Subgroup.map_bot]
  have hSB : GGRCSOmSummand BG := ggRCSOmSummand_of_isQuasisimple hBq hBZ
  obtain ⟨x', hx'W, hx'3, hy₀x'⟩ := exists_polar_eq_one_perp hQ h₁₂ h₁₃ h₂₃ hy₀ hy₀W hy₀3
  have hQB : QG ≤ ⁅QG ⊔ BG, QG ⊔ BG⁆ := by
    have h := Φ_mono (σ := σ) φ
      (rootRadical_le_commutator_omFix h₁₂ h₁₃ h₂₃ hy₀W hx'W hy₀3 hx'3 hy₀x')
    rwa [Φ_commutator hσ φ (sup_le hRE hL₂E) (sup_le hRE hL₂E), Φ_sup hσ φ hRE hL₂E] at h
  have hX₃ : ggRCSX φ.range (φ x) = QG ⊔ (AG ⊔ BG ⊔ ⊥) := by
    rw [hX, sup_bot_eq, sup_assoc]
  rcases card_eq_two_or_four_le K with hK | hK
  ·
    by_cases hp3 : p = 3
    ·
      refine Or.inr ⟨hp3, ?_⟩
      rw [hφr, ← hr]
      exact sThreeSetting_frame hK hQ hEΩ hOE h₁₂ h₁₃ h₂₃ hy₀ hy₀W hy₀3 hΩ hWq hWZ (h3 hK hp3)
        hσ hσE hx hxC ψ hψ u
    · obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
      have eS : ↥AG ≃* Equiv.Perm (Fin 3) := eA.trans e3
      have hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX φ.range (φ x)) = QG :=
        pCoreOf_eq_of_three_summands hX₃ hQ2 h1Q h2Q bot_le h12 (le_centralizer_bot _)
          (le_centralizer_bot _) (ggRCSOmSummand_of_perm eS) hSB ggRCSOmSummand_bot
      have hpA : ¬ p ∣ Nat.card AG := by
        rw [Nat.card_congr eS.toEquiv, card_perm_three]
        exact fun h => hp3 (eq_three_of_dvd_six hp hp2 h)
      exact Or.inl (ggRCSLayerQ_of_three_summands hp hp2 hG₀M hM hQ2 hO2
        (by rw [hX, sup_bot_eq]) h1Q h2Q bot_le h12 (le_centralizer_bot _)
        (le_centralizer_bot _) (fun h => absurd h hpA) (fun _ => ⟨hBq, hQB⟩)
        (ggRCSOmQuasiSummand_bot hp _))
  ·
    have hAq : CFSG.IsQuasisimple AG := CFSG.LocalCores.isQuasisimple_of_mulEquiv eA.symm
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK))
    have hAZ : center AG = ⊥ := by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eA.symm,
        center_SL2_eq_bot_of_charTwo, Subgroup.map_bot]
    have hQA : QG ≤ ⁅QG ⊔ AG, QG ⊔ AG⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_leviFix h₁₂ h₁₃ h₂₃)
      rwa [Φ_commutator hσ φ (sup_le hRE hL₁E) (sup_le hRE hL₁E), Φ_sup hσ φ hRE hL₁E] at h
    have hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX φ.range (φ x)) = QG :=
      pCoreOf_eq_of_three_summands hX₃ hQ2 h1Q h2Q bot_le h12 (le_centralizer_bot _)
        (le_centralizer_bot _) (ggRCSOmSummand_of_isQuasisimple hAq hAZ) hSB ggRCSOmSummand_bot
    exact Or.inl (ggRCSLayerQ_of_three_summands hp hp2 hG₀M hM hQ2 hO2 (by rw [hX, sup_bot_eq])
      h1Q h2Q bot_le h12 (le_centralizer_bot _) (le_centralizer_bot _) (fun _ => ⟨hAq, hQA⟩)
      (fun _ => ⟨hBq, hQB⟩) (ggRCSOmQuasiSummand_bot hp _))

end Frame

section Four

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open scoped MatrixGroups

theorem ggRCSLayerQ_frame_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) (F : HypFrame Q 4)
    (hF0 : ∀ x : V, (∀ k u, polar Q (F.vec k u) x = 0) → x = 0) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (s t : Bool) {c : K} (hc : c ≠ 0) (h23 : Nat.card K = 2 → p ≠ 3)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U}
    (hx : σ x = eichler Q (F.vec j t) (c • F.vec i s))
    (hxC : centralizer {x} ≤ ggOTwoPrime (centralizer {x}))
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) (u : U) :
    GGRCSLayerQ p ψ.range M (ψ (u * x * u⁻¹)) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hE : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
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
  set φ := ψ.comp (MulAut.conj u).toMonoidHom with hφdef
  have hφ : Function.Injective φ := RCSTSp.comp_conj_injective hψ u
  have hφr : φ.range = ψ.range := RCSTSp.range_comp_conj ψ u
  have hr : ψ (u * x * u⁻¹) = φ x := by
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr, ← hφr]
  rw [← hφr] at hG₀M hM
  have hRE : rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc) ≤ σ.range :=
    hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) (framePair F j t) (smulPair (framePair F i s) hc) ≤
      σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q (framePair F j t) (smulPair (framePair F i s) hc) ≤ σ.range :=
    hσE ▸ fun g hg => (mem_omFix.mp hg).1
  set QG := Φ σ φ (rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)) with hQGdef
  set AG := Φ σ φ (leviFix (elementaryGroup Q) (framePair F j t)
    (smulPair (framePair F i s) hc)) with hAGdef
  set BG := Φ σ φ (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)) with hBGdef
  have hX : ggRCSX φ.range (φ x) = QG ⊔ AG ⊔ BG := by
    have hx' : σ x = eichler Q (framePair F j t).e (smulPair (framePair F i s) hc).e := hx
    rw [RCSTSp.ggRCSX_eq_map_centralizer φ hφ hxC, centralizer_eq_comap hσ hσE x, hx',
      centralizer_inf_elementaryGroup_eq h₁₂]
    change Φ σ φ _ = _
    rw [Φ_sup hσ φ (sup_le hRE hL₁E) hL₂E, Φ_sup hσ φ hRE hL₁E]
  have hQ2 : IsPGroup 2 QG := Φ_isPGroup φ hσ isPGroup_rootRadical
  have h1Q : AG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (leviFix_le_normalizer_rootRadical h₁₂)
  have h2Q : BG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (omFix_le_normalizer_rootRadical h₁₂)
  have h12 : AG ≤ centralizer (BG : Set G) :=
    Φ_le_centralizer hσ φ (leviFix_le_centralizer_omFix h₁₂)
  have eA : ↥AG ≃* SL(2, K) := (Φ_equiv hσ φ hφ hL₁E).trans (leviFixEquiv _ _ h₁₂ hE)
  rcases card_eq_two_or_four_le K with hK | hK
  ·
    have hp3 := h23 hK
    obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
    have hpA : ¬ p ∣ Nat.card AG := by
      rw [Nat.card_congr (eA.trans e3).toEquiv, card_perm_three]
      exact fun h => hp3 (eq_three_of_dvd_six hp hp2 h)
    have hpB : ¬ p ∣ Nat.card BG := by
      rw [Nat.card_congr (Φ_equiv hσ φ hφ hL₂E).toEquiv]
      intro hpd
      have hdvd : Nat.card (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)) ∣
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub (framePair F j t)
            (smulPair (framePair F i s) hc)))) := by
        rw [Nat.card_congr (MonoidHom.ofInjective (resW_injective (Q := Q) h₁₂)).toEquiv]
        refine Subgroup.card_dvd_of_le ?_
        rintro _ ⟨g, rfl⟩
        exact resW_mem_orthogonalGroup g
      rcases eq_two_or_three_of_dvd_card_four hR hdim hS hK hp (dvd_trans hpd hdvd) with h | h
      · exact hp2 h
      · exact hp3 h
    refine ⟨∅, fun _ h => absurd h (Set.notMem_empty _), fun y hy hyp => ?_⟩
    have hy1 : y ∈ AG ⊔ (QG ⊔ BG) := by
      have e : ggRCSX φ.range (φ x) = AG ⊔ (QG ⊔ BG) := by rw [hX]; ac_rfl
      rw [← e]
      exact hy
    have hy2 := ggRCST_mem_of_mem_sup_coprime hp hpA
      (le_normalizer_sup_of_centralizer h1Q h12) hy1 hyp
    have hy3 := ggRCST_mem_of_mem_sup_coprime hp hpB h2Q (by rwa [sup_comm] at hy2) hyp
    rw [ggRCS_eq_one_of_mem_two hp hp2 hQ2 hy3 hyp]
    exact one_mem _
  ·
    have hΩ := omegaGroup_le_orthDerived_of_splitFour hR hdim hS hK
    have hcardR := card_orthDerived_le_four hR hdim hS hK
    have hLa := leviFix_le_omFix (Q := Q) h₁₃ h₁₄ h₂₃ h₂₄
    have hLb := leviFix_le_omFix (Q := Q) h₁₃ h₁₄' h₂₃ h₂₄'
    have hab := leviFix_le_centralizer_flip h₃₄ hE hE
    have hdisj := leviFix_inf_flip_eq_bot (Q := Q) h₃₄
    have hcard' : Nat.card (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)) ≤
        Nat.card (leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true)) *
          Nat.card (leviFix (elementaryGroup Q) (framePair F k true)
            (flipPair (framePair F l true))) := by
      rw [Nat.card_congr (omFixEquiv h₁₂ hQ hEΩ hOE hR hΩ).toEquiv,
        Nat.card_congr (leviFixEquiv _ _ h₃₄ hE).toEquiv,
        Nat.card_congr (leviFixEquiv _ _ h₃₄' hE).toEquiv, ← _root_.sq]
      exact hcardR
    have hgen : omFix Q (framePair F j t) (smulPair (framePair F i s) hc) =
        leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true) ⊔
          leviFix (elementaryGroup Q) (framePair F k true) (flipPair (framePair F l true)) := by
      refine le_antisymm (fun g hg => ?_) (sup_le hLa hLb)
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_card_le hLa hLb hab hdisj hcard' g hg
      exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
    have hLaE : leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true) ≤
        σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
    have hLbE : leviFix (elementaryGroup Q) (framePair F k true)
        (flipPair (framePair F l true)) ≤ σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
    set B1G := Φ σ φ (leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true))
      with hB1Gdef
    set B2G := Φ σ φ (leviFix (elementaryGroup Q) (framePair F k true)
      (flipPair (framePair F l true))) with hB2Gdef
    have hBG : BG = B1G ⊔ B2G := by rw [hBGdef, hgen, Φ_sup hσ φ hLaE hLbE]
    have hX4 : ggRCSX φ.range (φ x) = QG ⊔ AG ⊔ B1G ⊔ B2G := by rw [hX, hBG, ← sup_assoc]
    have hSL : CFSG.IsQuasisimple SL(2, K) :=
      CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK)
    have qz : ∀ L : Subgroup G, (↥L ≃* SL(2, K)) → CFSG.IsQuasisimple L ∧ center L = ⊥ :=
      fun L e => ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSL, by
        rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e.symm,
          center_SL2_eq_bot_of_charTwo, Subgroup.map_bot]⟩
    obtain ⟨hAq, hAZ⟩ := qz AG eA
    obtain ⟨hB1q, hB1Z⟩ := qz B1G ((Φ_equiv hσ φ hφ hLaE).trans (leviFixEquiv _ _ h₃₄ hE))
    obtain ⟨hB2q, hB2Z⟩ := qz B2G ((Φ_equiv hσ φ hφ hLbE).trans (leviFixEquiv _ _ h₃₄' hE))
    have hB1Q : B1G ≤ normalizer (QG : Set G) :=
      Φ_le_normalizer φ (hLa.trans (omFix_le_normalizer_rootRadical h₁₂))
    have hB2Q : B2G ≤ normalizer (QG : Set G) :=
      Φ_le_normalizer φ (hLb.trans (omFix_le_normalizer_rootRadical h₁₂))
    have hAB1 : AG ≤ centralizer (B1G : Set G) :=
      Φ_le_centralizer hσ φ (leviFix_le_centralizer_of_orth h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ _ _)
    have hAB2 : AG ≤ centralizer (B2G : Set G) :=
      Φ_le_centralizer hσ φ (leviFix_le_centralizer_of_orth h₁₂ h₁₃ h₁₄' h₂₃ h₂₄' _ _)
    have hB12 : B1G ≤ centralizer (B2G : Set G) := Φ_le_centralizer hσ φ hab
    have hQA : QG ≤ ⁅QG ⊔ AG, QG ⊔ AG⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_leviFix h₁₂ h₁₃ h₂₃)
      rwa [Φ_commutator hσ φ (sup_le hRE hL₁E) (sup_le hRE hL₁E), Φ_sup hσ φ hRE hL₁E] at h
    have hQB1 : QG ≤ ⁅QG ⊔ B1G, QG ⊔ B1G⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_sl h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hspan₁
        (H := rootRadical Q _ _ ⊔ leviFix (elementaryGroup Q) (framePair F k true)
          (framePair F l true)) le_sup_left
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄ hE t).1)
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄ hE t).2))
      rwa [Φ_commutator hσ φ (sup_le hRE hLaE) (sup_le hRE hLaE), Φ_sup hσ φ hRE hLaE] at h
    have hQB2 : QG ≤ ⁅QG ⊔ B2G, QG ⊔ B2G⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_sl h₁₂ h₁₃ h₁₄' h₂₃ h₂₄' h₃₄'
        hspan₂ (H := rootRadical Q _ _ ⊔ leviFix (elementaryGroup Q) (framePair F k true)
          (flipPair (framePair F l true))) le_sup_left
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄' hE t).1)
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄' hE t).2))
      rwa [Φ_commutator hσ φ (sup_le hRE hLbE) (sup_le hRE hLbE), Φ_sup hσ φ hRE hLbE] at h
    have hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX φ.range (φ x)) = QG :=
      pCoreOf_eq_of_three_summands (by rw [hX4]; ac_rfl) hQ2 h1Q hB1Q hB2Q hAB1 hAB2 hB12
        (ggRCSOmSummand_of_isQuasisimple hAq hAZ) (ggRCSOmSummand_of_isQuasisimple hB1q hB1Z)
        (ggRCSOmSummand_of_isQuasisimple hB2q hB2Z)
    exact ggRCSLayerQ_of_three_summands hp hp2 hG₀M hM hQ2 hO2 hX4 h1Q hB1Q hB2Q hAB1 hAB2 hB12
      (fun _ => ⟨hAq, hQA⟩) (fun _ => ⟨hB1q, hQB1⟩) (fun _ => ⟨hB2q, hQB2⟩)

end Four

section Five

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {N : ℕ} (F : HypFrame Q N)

theorem ggRCSLayerNbr_hypFrame_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) {i j k l m : Fin N} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l)
    (hkm : k ≠ m) (hlm : l ≠ m) (s t : Bool) {c : K} (hc : c ≠ 0)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U}
    (hx : σ x = eichler Q (F.vec j t) (c • F.vec i s))
    (hxC : centralizer {x} ≤ ggOTwoPrime (centralizer {x}))
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) (u : U) :
    GGRCSLayerNbr p ψ.range M (ψ (u * x * u⁻¹)) := by
  have h₁₂ := orth₁₂ F hij s t hc
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  have hT := exists_totallySingular_wSub F hik hil him hjk hjl hjm hkl hkm hlm s t hc
  have : Finite V := Module.finite_of_finite K
  exact ggRCSLayerNbr_frame (P₃ := framePair F l true) hp hp2 hQ hEΩ hOE h₁₂ (orth₁₃ F hjl t true)
    (orth₂₃ F hil s true hc) (y₀ := F.vec k true) (framePair F k true).e_ne_zero
    (inW_frame F hc (fun v => F.polar_vec_of_ne hik v true) (fun v => F.polar_vec_of_ne hjk v true))
    ⟨F.polar_vec_of_ne hkl.symm true true, F.polar_vec_of_ne hkl.symm false true⟩
    (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT)
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)
    (center_orthDerived_eq_bot' hR hT (exists_restrict_ne_zero F hik hjk hc))
    (fun hK _ => three_dvd_card_omFix F hik hil hjk hjl hkl s t hc hK) hσ hσE hx hxC ψ hψ hG₀M hM u

end Five

end RCSTOm

namespace RCSTOm

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)

section Minus

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem ggRCSLayerNbr_minus_small {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    {a : K} (ha : a ≠ 0) {G : Type} [Group G] [Finite G] (ψ : spinGroup (quadMinus n K b c) →* G)
    (hψ : Function.Injective ψ) {M : Subgroup G} (hG₀M : ψ.range ≤ M)
    (hM : M ≤ normalizer (ψ.range : Set G)) (u : spinGroup (quadMinus n K b c)) :
    GGRCSLayerNbr p ψ.range M (ψ (u * (minusFrame n b c).longRoot hij s t (.ofAdd a) * u⁻¹)) := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have h₁₂ := orth₁₂ (minusFrame n b c).toHypFrame hij s t ha
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  have hdimW : finrank K (wSub (framePair (minusFrame n b c).toHypFrame j t)
      (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)) = 2 * n - 4 := by
    have := finrank_wSub_add_four (Q := quadMinus n K b c) h₁₂
    rw [finrank_quadMinus (by omega)] at this
    omega
  have hEΩ := elementaryGroup_quadMinus_le_omegaGroup hirr hn4
  have hOE : orthDerived (quadMinus n K b c) ≤ elementaryGroup (quadMinus n K b c) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn4 hirr]
  obtain ⟨k, hik, hjk⟩ := exists_one_ne (by omega : 3 ≤ n - 1) i j
  have hz0 : (minusFrame n b c).z ≠ 0 := fun h => by
    have h1 := (minusFrame n b c).map_z
    rw [h, QuadraticMap.map_zero] at h1
    exact zero_ne_one h1
  have hz : ∀ (l : Fin (n - 1)) (v : Bool),
      polar (quadMinus n K b c) ((minusFrame n b c).vec l v) (minusFrame n b c).z = 0 :=
    fun l v => (minusFrame n b c).polar_vec_z l v
  have hσx := spinAction_longRoot_eq_eichler (minusFrame n b c).toHypFrame hij s t a
  have hxC := centralizer_longRoot_minus_le hirr hn4 hij s t ha
  have hzW := inW_frame (minusFrame n b c).toHypFrame (s := s) (t := t) ha (hz i) (hz j)
  have hts : ∀ U : Submodule K (wSub (framePair (minusFrame n b c).toHypFrame j t)
      (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)), finrank K U = n - 2 →
      ∃ u ∈ U, (quadMinus n K b c).restrict _ u ≠ 0 := fun U hU =>
    exists_restrict_ne_zero_minus (by omega) hirr h₁₂ U hU
  rcases (show n = 4 ∨ n = 5 by omega) with rfl | rfl
  ·
    have hdim : finrank K (wSub (framePair (minusFrame 4 b c).toHypFrame j t)
        (smulPair (framePair (minusFrame 4 b c).toHypFrame i s) ha)) = 4 := by
      rw [hdimW]
    obtain ⟨hWq, hWZ, hcard⟩ := isQuasisimple_orthDerived_of_four hR hdim hts
    have hΩ := omegaGroup_le_orthDerived_of_four hR hdim hts
    refine ggRCSLayerNbr_frame (P₃ := framePair (minusFrame 4 b c).toHypFrame k true) hp hp2 hQ hEΩ
      hOE h₁₂ (orth₁₃ _ hjk t true) (orth₂₃ _ hik s true ha) hz0 hzW ⟨hz k true, hz k false⟩
      hΩ hWq hWZ (fun hK _ => ?_) (spinAction_quadMinus_injective hirr)
      (range_spinAction_quadMinus hn4 hirr) hσx hxC ψ hψ hG₀M hM u
    rw [Nat.card_congr (omFixEquiv h₁₂ hQ hEΩ hOE hR hΩ).toEquiv, hcard, hK]
    norm_num
  ·
    have hdim : finrank K (wSub (framePair (minusFrame 5 b c).toHypFrame j t)
        (smulPair (framePair (minusFrame 5 b c).toHypFrame i s) ha)) = 6 := by
      rw [hdimW]
    obtain ⟨hWq, hWZ⟩ := isQuasisimple_orthDerived_of_six hR hdim hts
    have hΩ := omegaGroup_le_orthDerived_of_six hR hdim hts
    obtain ⟨k', l', hik', hil', hjk', hjl', hkl'⟩ := exists_two_ne (by norm_num : 4 ≤ 5 - 1) i j
    have : Finite (Fin (5 - 1) ⊕ Fin (5 - 1) ⊕ Fin 2 → K) := Module.finite_of_finite K
    exact ggRCSLayerNbr_frame (P₃ := framePair (minusFrame 5 b c).toHypFrame k true) hp hp2 hQ hEΩ
      hOE h₁₂ (orth₁₃ _ hjk t true) (orth₂₃ _ hik s true ha) hz0 hzW ⟨hz k true, hz k false⟩
      hΩ hWq hWZ (fun hK _ => three_dvd_card_omFix _ hik' hil' hjk' hjl' hkl' s t ha hK)
      (spinAction_quadMinus_injective hirr) (range_spinAction_quadMinus hn4 hirr) hσx hxC ψ hψ
      hG₀M hM u

end Minus

end RCSTOm

section TagPlus

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal

theorem ggRCSLayerNbr_POmegaPlus {G : Type} [Group G] [Finite G] {p n f : ℕ}
    (ψ : (ggU .POmegaPlus n f).K →* G) (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .POmegaPlus n 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus n f).K) {r : G}
    (hr : GGRootInvolution (ggU .POmegaPlus n f).D .POmegaPlus ψ r)
    (h23 : n = 4 → f = 1 → p ≠ 3) :
    GGRCSLayerNbr p ψ.range (Subgroup.normalizer (ψ.range : Set G)) r := by
  obtain ⟨-, hf1, hn4⟩ := hadm
  have hn : 3 ≤ n := by omega
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hker hr
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn).le
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  obtain ⟨i, j, hij, s, t, -, hX⟩ := exists_plusRootGroup_eq (K := GaloisField 2 f) hn hγ
  have hx' : x ∈ ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t).range := by
    rw [← hX]
    exact hx
  obtain ⟨c₀, rfl⟩ := hx'
  have hc : Multiplicative.toAdd c₀ ≠ 0 := by
    intro h0
    have hc₀ : c₀ = 1 := by rw [← ofAdd_toAdd c₀, h0, ofAdd_zero]
    rw [hc₀, map_one, mul_one, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hσx : spinAction (quadPlus n (GaloisField 2 f))
      ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t c₀) =
      eichler (quadPlus n (GaloisField 2 f)) ((plusFrame n (GaloisField 2 f) hn).vec j t)
        (Multiplicative.toAdd c₀ • (plusFrame n (GaloisField 2 f) hn).vec i s) := by
    rw [← RootCentOmega.spinAction_longRoot_eq_eichler, ofAdd_toAdd]
  have hOE : CFSG.RankThree.Classical2.orthDerived (quadPlus n (GaloisField 2 f)) ≤
      elementaryGroup (quadPlus n (GaloisField 2 f)) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadPlus hn]
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  ·
    obtain ⟨k, l, hik, hil, hjk, hjl, hkl⟩ := RCSTOm.exists_two_ne le_rfl i j
    have h23' : Nat.card (GaloisField 2 f) = 2 → p ≠ 3 := fun hK => by
      refine h23 rfl ?_
      rw [GaloisField.card 2 f (by omega)] at hK
      have h2 : (2 : ℕ) ^ f = 2 ^ 1 := by rw [hK, pow_one]
      exact Nat.pow_right_injective le_rfl h2
    exact Or.inl (RCSTOm.ggRCSLayerQ_frame_four hp hp2 (nondegenerate_polarBilin_quadPlus 4 _)
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE
      (plusFrame 4 (GaloisField 2 f) hn) (fun x hx => RootCentOmega.eq_zero_of_polar_plusVec hx)
      hij hik hil hjk hjl hkl s t hc h23' RootCentOmega.spinAction_quadPlus_injective
      (range_spinAction_quadPlus hn) hσx (RootCentOmega.centralizer_longRoot_plus_le hn4 hij s t hc)
      ψ hinj Subgroup.le_normalizer le_rfl u)
  · obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
      RCSTOm.exists_three_ne hn5 i j
    exact RCSTOm.ggRCSLayerNbr_hypFrame_five (plusFrame n (GaloisField 2 f) hn) hp hp2
      (nondegenerate_polarBilin_quadPlus n (GaloisField 2 f))
      (RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn) hOE hij hik hil him hjk hjl hjm
      hkl hkm hlm s t hc RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus hn)
      hσx (RootCentOmega.centralizer_longRoot_plus_le hn4 hij s t hc) ψ hinj
      Subgroup.le_normalizer le_rfl u


theorem ggRootCentLayerNbrTag_POmegaPlus : GGRootCentLayerNbrTag .POmegaPlus := by
  intro G _ _ n f ψ hadm _ hker _ _ hn4 r hr
  exact ggRCSLayerNbr_POmegaPlus ψ Nat.prime_three (by norm_num) hadm hker hr
    fun hn hf _ => hn4 (Or.inr (Or.inr rfl)) hn hf

end TagPlus

section TagMinus

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)

theorem ggRootCentLayerNbrTag_POmegaMinus : GGRootCentLayerNbrTag .POmegaMinus := by
  intro G _ _ n f ψ hadm _ hker _ _ _ r hr
  obtain ⟨-, -, hn⟩ := hadm
  have hirr := minusCoeffs_irr 2 f
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (PsiDiag.SpinM.center_eq_bot (K := GaloisField 2 f) hirr hn).le
  obtain ⟨hr2, γ, ⟨-, hγl⟩, u, hru⟩ := hr
  obtain ⟨i, j, hij, s, t, hst⟩ :=
    RootCentOmega.exists_long_of_ggLongRoot_minus hirr hn (hγl (Or.inr (Or.inl rfl)))
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hst).mp hx
  have ha : a ≠ 0 := by
    rintro rfl
    exact hx1 (map_one _)
  rcases (show n ≤ 5 ∨ 6 ≤ n by omega) with hn5 | hn6
  · exact RCSTOm.ggRCSLayerNbr_minus_small Nat.prime_three (by norm_num) hn hn5 hirr hij s t ha
      ψ hinj Subgroup.le_normalizer le_rfl u
  · obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
      RCSTOm.exists_three_ne (by omega : 5 ≤ n - 1) i j
    refine RCSTOm.ggRCSLayerNbr_hypFrame_five _ Nat.prime_three (by norm_num)
      (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) hirr)
      (elementaryGroup_quadMinus_le_omegaGroup hirr hn) ?_ hij hik hil him hjk hjl hjm hkl hkm
      hlm s t ha (spinAction_quadMinus_injective hirr) (range_spinAction_quadMinus hn hirr)
      (spinAction_longRoot_eq_eichler _ hij s t a)
      (centralizer_longRoot_minus_le hirr hn hij s t ha) ψ hinj Subgroup.le_normalizer le_rfl u
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn hirr]

end TagMinus

end CFSG.StandardType
