module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmFour
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSummand
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarking
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.Quasithin.Background.SzG11G94Solv

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

theorem exists_kgPieces_frame_four {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) (F : HypFrame Q 4)
    (hF0 : ∀ x : V, (∀ k u, polar Q (F.vec k u) x = 0) → x = 0) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (s t : Bool) {c : K} (hc : c ≠ 0)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U}
    (hx : σ x = eichler Q (F.vec j t) (c • F.vec i s))
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) (u : U)
    {E : Subgroup G} (hE : E ≤ ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)}) :
    ∃ 𝒥 : Set (Subgroup G),
      (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)} →
        ⁅P, P⁆ = P → P ≤ sSup 𝒥) ∧
      ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)}) E J := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
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
  set φ := ψ.comp (MulAut.conj u).toMonoidHom with hφdef
  have hφ : Function.Injective φ := RCSTSp.comp_conj_injective hψ u
  have hφr : φ.range = ψ.range := RCSTSp.range_comp_conj ψ u
  have hr : ψ (u * x * u⁻¹) = φ x := by
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  set C₀ : Subgroup G := ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)} with hC₀def
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
  have hx' : σ x = eichler Q (framePair F j t).e (smulPair (framePair F i s) hc).e := hx
  have hC₀X : C₀ = QG ⊔ AG ⊔ BG := by
    rw [hC₀def, hr, ← hφr, RCSTSp.range_inf_centralizer_of_injective hφ x,
      centralizer_eq_comap hσ hσE x, hx', centralizer_inf_elementaryGroup_eq h₁₂]
    change Φ σ φ _ = _
    rw [Φ_sup hσ φ (sup_le hRE hL₁E) hL₂E, Φ_sup hσ φ hRE hL₁E]
  have hQ2 : IsPGroup 2 QG := Φ_isPGroup φ hσ isPGroup_rootRadical
  have h1Q : AG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (leviFix_le_normalizer_rootRadical h₁₂)
  have h2Q : BG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (omFix_le_normalizer_rootRadical h₁₂)
  have h12 : AG ≤ centralizer (BG : Set G) :=
    Φ_le_centralizer hσ φ (leviFix_le_centralizer_omFix h₁₂)
  have hdQL : Disjoint QG (AG ⊔ BG) := by
    have h := Φ_disjoint hσ φ hφ (disjoint_rootRadical_sup h₁₂)
    rwa [Φ_sup hσ φ hL₁E hL₂E] at h
  have hdST : Disjoint AG BG := Φ_disjoint hσ φ hφ (disjoint_leviFix_omFix h₁₂)
  have eA : ↥AG ≃* SL(2, K) := (Φ_equiv hσ φ hφ hL₁E).trans (leviFixEquiv _ _ h₁₂ hEich)
  rcases card_eq_two_or_four_le K with hK | hK
  ·
    obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
    have hAGcard : Nat.card AG = 6 := by
      rw [Nat.card_congr (eA.trans e3).toEquiv, card_perm_three]
    have hBGdvd : Nat.card BG ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (Q.restrict (wSub (framePair F j t) (smulPair (framePair F i s) hc)))) := by
      rw [Nat.card_congr (Φ_equiv hσ φ hφ hL₂E).toEquiv]
      rw [Nat.card_congr (MonoidHom.ofInjective (resW_injective (Q := Q) h₁₂)).toEquiv]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨g, rfl⟩
      exact resW_mem_orthogonalGroup g
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    have hcardC : Nat.card C₀ = Nat.card QG * (Nat.card AG * Nat.card BG) := by
      rw [show C₀ = QG ⊔ (AG ⊔ BG) from by rw [hC₀X]; ac_rfl,
        CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer QG (AG ⊔ BG)
          (sup_le h1Q h2Q) hdQL,
        CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer AG BG
          ((Subgroup.le_centralizer_iff.mp h12).trans
            (Subgroup.centralizer_le_normalizer (AG : Set G))) hdST]
    have hsolC : Group.IsSolvable ↥C₀ := by
      refine CFSG.Quasithin.SzG11G94.isSolvable_of_prime_divisors (p := 2) (q := 3) ?_
      intro r hr hrd
      rw [hcardC, hn, hAGcard] at hrd
      rcases hr.dvd_mul.mp hrd with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h))
      · rcases hr.dvd_mul.mp h with h6 | hB
        · have h23 : r ∣ 2 * 3 := by simpa using h6
          rcases hr.dvd_mul.mp h23 with h2 | h3
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
          · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
        · exact eq_two_or_three_of_dvd_card_four hR hdim hS hK hr (dvd_trans hB hBGdvd)
    refine ⟨∅, ?_, ?_⟩
    · intro P hPC hperfP
      rw [sSup_empty]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperfP
      haveI : Group.IsSolvable ↥C₀ := hsolC
      haveI : Group.IsSolvable ↥P :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPC)
          (Subgroup.inclusion_injective hPC)
      haveI : Nontrivial ↥P :=
        ⟨⟨y, hy⟩, 1, fun h => hy1 (by simpa using congrArg Subtype.val h)⟩
      exact Group.IsPerfect.not_isSolvable ↥P inferInstance
    · intro J hJ
      exact absurd hJ (Set.notMem_empty J)
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hcardK⟩ := FiniteField.card K 2
    have hKf : Nat.card K = 2 ^ (f : ℕ) := by
      rw [Nat.card_eq_fintype_card, hcardK]
    have hf2 : 2 ≤ (f : ℕ) := by
      by_contra h
      push Not at h
      rcases (by omega : (f : ℕ) = 0 ∨ (f : ℕ) = 1) with h0 | h1
      · rw [hKf, h0] at hK
        norm_num at hK
      · rw [hKf, h1] at hK
        norm_num at hK
    have hΩ := omegaGroup_le_orthDerived_of_splitFour hR hdim hS hK
    have hcardR := card_orthDerived_le_four hR hdim hS hK
    have hLa := leviFix_le_omFix (Q := Q) h₁₃ h₁₄ h₂₃ h₂₄
    have hLb := leviFix_le_omFix (Q := Q) h₁₃ h₁₄' h₂₃ h₂₄'
    have hab := leviFix_le_centralizer_flip h₃₄ hEich hEich
    have hdisj := leviFix_inf_flip_eq_bot (Q := Q) h₃₄
    have hcard' : Nat.card (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)) ≤
        Nat.card (leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true)) *
          Nat.card (leviFix (elementaryGroup Q) (framePair F k true)
            (flipPair (framePair F l true))) := by
      rw [Nat.card_congr (omFixEquiv h₁₂ hQ hEΩ hOE hR hΩ).toEquiv,
        Nat.card_congr (leviFixEquiv _ _ h₃₄ hEich).toEquiv,
        Nat.card_congr (leviFixEquiv _ _ h₃₄' hEich).toEquiv, ← _root_.sq]
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
    have hC₀X4 : C₀ = QG ⊔ AG ⊔ B1G ⊔ B2G := by rw [hC₀X, hBG, ← sup_assoc]
    have eB1 : ↥B1G ≃* SL(2, K) :=
      (Φ_equiv hσ φ hφ hLaE).trans (leviFixEquiv _ _ h₃₄ hEich)
    have eB2 : ↥B2G ≃* SL(2, K) :=
      (Φ_equiv hσ φ hφ hLbE).trans (leviFixEquiv _ _ h₃₄' hEich)
    have hB1Q : B1G ≤ normalizer (QG : Set G) :=
      Φ_le_normalizer φ (hLa.trans (omFix_le_normalizer_rootRadical h₁₂))
    have hB2Q : B2G ≤ normalizer (QG : Set G) :=
      Φ_le_normalizer φ (hLb.trans (omFix_le_normalizer_rootRadical h₁₂))
    have hAB1 : AG ≤ centralizer (B1G : Set G) :=
      Φ_le_centralizer hσ φ (leviFix_le_centralizer_of_orth h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ _ _)
    have hAB2 : AG ≤ centralizer (B2G : Set G) :=
      Φ_le_centralizer hσ φ (leviFix_le_centralizer_of_orth h₁₂ h₁₃ h₁₄' h₂₃ h₂₄' _ _)
    have hB12 : B1G ≤ centralizer (B2G : Set G) := Φ_le_centralizer hσ φ hab
    have hB1BG : B1G ≤ BG := Φ_mono (σ := σ) φ hLa
    have hB2BG : B2G ≤ BG := Φ_mono (σ := σ) φ hLb
    have hQA : QG ≤ ⁅QG ⊔ AG, QG ⊔ AG⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_leviFix h₁₂ h₁₃ h₂₃)
      rwa [Φ_commutator hσ φ (sup_le hRE hL₁E) (sup_le hRE hL₁E), Φ_sup hσ φ hRE hL₁E] at h
    have hQB1 : QG ≤ ⁅QG ⊔ B1G, QG ⊔ B1G⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_sl h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hspan₁
        (H := rootRadical Q _ _ ⊔ leviFix (elementaryGroup Q) (framePair F k true)
          (framePair F l true)) le_sup_left
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄ hEich t).1)
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄ hEich t).2))
      rwa [Φ_commutator hσ φ (sup_le hRE hLaE) (sup_le hRE hLaE), Φ_sup hσ φ hRE hLaE] at h
    have hQB2 : QG ≤ ⁅QG ⊔ B2G, QG ⊔ B2G⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_sl h₁₂ h₁₃ h₁₄' h₂₃ h₂₄' h₃₄'
        hspan₂ (H := rootRadical Q _ _ ⊔ leviFix (elementaryGroup Q) (framePair F k true)
          (flipPair (framePair F l true))) le_sup_left
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄' hEich t).1)
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄' hEich t).2))
      rwa [Φ_commutator hσ φ (sup_le hRE hLbE) (sup_le hRE hLbE), Φ_sup hσ φ hRE hLbE] at h
    have hSL : CFSG.IsQuasisimple SL(2, K) :=
      CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK)
    have qz : ∀ L : Subgroup G, (↥L ≃* SL(2, K)) → CFSG.IsQuasisimple L ∧ center L = ⊥ :=
      fun L e => ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSL, by
        rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e.symm,
          center_SL2_eq_bot_of_charTwo, Subgroup.map_bot]⟩
    obtain ⟨hAq, hAZ⟩ := qz AG eA
    obtain ⟨hB1q, hB1Z⟩ := qz B1G eB1
    obtain ⟨hB2q, hB2Z⟩ := qz B2G eB2
    have hO2 : CFSG.Assembly.pCoreOf 2 C₀ = QG :=
      pCoreOf_eq_of_three_summands (by rw [hC₀X4]; ac_rfl) hQ2 h1Q hB1Q hB2Q hAB1 hAB2 hB12
        (ggRCSOmSummand_of_isQuasisimple hAq hAZ) (ggRCSOmSummand_of_isQuasisimple hB1q hB1Z)
        (ggRCSOmSummand_of_isQuasisimple hB2q hB2Z)
    obtain ⟨hAq', hAm⟩ := isQuasisimple_largeEvenMarking_of_equiv_SL2 hKf hf2 eA
    obtain ⟨hB1q', hB1m⟩ := isQuasisimple_largeEvenMarking_of_equiv_SL2 hKf hf2 eB1
    obtain ⟨hB2q', hB2m⟩ := isQuasisimple_largeEvenMarking_of_equiv_SL2 hKf hf2 eB2
    let 𝒥 : Set (Subgroup G) := {QG ⊔ AG, QG ⊔ B1G, QG ⊔ B2G}
    refine ⟨𝒥, ?_, ?_⟩
    · intro P hP _
      have hmem1 : QG ⊔ AG ∈ 𝒥 := Or.inl rfl
      have hmem2 : QG ⊔ B1G ∈ 𝒥 := Or.inr (Or.inl rfl)
      have hmem3 : QG ⊔ B2G ∈ 𝒥 := Or.inr (Or.inr rfl)
      have hQ : QG ≤ sSup 𝒥 := (le_sup_left : QG ≤ QG ⊔ AG).trans (le_sSup hmem1)
      have hA : AG ≤ sSup 𝒥 := (le_sup_right : AG ≤ QG ⊔ AG).trans (le_sSup hmem1)
      have hB1 : B1G ≤ sSup 𝒥 := (le_sup_right : B1G ≤ QG ⊔ B1G).trans (le_sSup hmem2)
      have hB2 : B2G ≤ sSup 𝒥 := (le_sup_right : B2G ≤ QG ⊔ B2G).trans (le_sSup hmem3)
      refine hP.trans ?_
      rw [hC₀X4]
      exact sup_le (sup_le (sup_le hQ hA) hB1) hB2
    · intro J hJ
      change J = QG ⊔ AG ∨ J = QG ⊔ B1G ∨ J = QG ⊔ B2G at hJ
      rcases hJ with rfl | rfl | rfl
      · have hAGperf : ⁅AG, AG⁆ = AG := Subgroup.isPerfect_iff.mp hAq.1
        refine ggRCSKGPiece_of_summand (C₀ := C₀) (E := E) (Q := QG) (L := AG)
          (M := B1G ⊔ B2G) ?_ hO2 h1Q (sup_le hB1Q hB2Q) ?_ ?_ ?_ hAq' hAm hE
        · rw [hC₀X4]; ac_rfl
        · exact Subgroup.le_centralizer_iff.mpr
            (sup_le (Subgroup.le_centralizer_iff.mp hAB1)
              (Subgroup.le_centralizer_iff.mp hAB2))
        · exact le_bot_iff.mp ((inf_le_inf_left QG (le_sup_left : AG ≤ AG ⊔ BG)).trans
            (le_of_eq (disjoint_iff.mp hdQL)))
        · refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQA ?_)
          calc AG = ⁅AG, AG⁆ := hAGperf.symm
            _ ≤ ⁅QG ⊔ AG, QG ⊔ AG⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
      · have hB1perf : ⁅B1G, B1G⁆ = B1G := Subgroup.isPerfect_iff.mp hB1q.1
        refine ggRCSKGPiece_of_summand (C₀ := C₀) (E := E) (Q := QG) (L := B1G)
          (M := AG ⊔ B2G) ?_ hO2 hB1Q (sup_le h1Q hB2Q) ?_ ?_ ?_ hB1q' hB1m hE
        · rw [hC₀X4]; ac_rfl
        · exact Subgroup.le_centralizer_iff.mpr
            (sup_le hAB1 (Subgroup.le_centralizer_iff.mp hB12))
        · exact le_bot_iff.mp ((inf_le_inf_left QG
            (hB1BG.trans (le_sup_right : BG ≤ AG ⊔ BG))).trans
            (le_of_eq (disjoint_iff.mp hdQL)))
        · refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQB1 ?_)
          calc B1G = ⁅B1G, B1G⁆ := hB1perf.symm
            _ ≤ ⁅QG ⊔ B1G, QG ⊔ B1G⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
      · have hB2perf : ⁅B2G, B2G⁆ = B2G := Subgroup.isPerfect_iff.mp hB2q.1
        refine ggRCSKGPiece_of_summand (C₀ := C₀) (E := E) (Q := QG) (L := B2G)
          (M := AG ⊔ B1G) ?_ hO2 hB2Q (sup_le h1Q hB1Q) ?_ ?_ ?_ hB2q' hB2m hE
        · rw [hC₀X4]; ac_rfl
        · exact Subgroup.le_centralizer_iff.mpr (sup_le hAB2 hB12)
        · exact le_bot_iff.mp ((inf_le_inf_left QG
            (hB2BG.trans (le_sup_right : BG ≤ AG ⊔ BG))).trans
            (le_of_eq (disjoint_iff.mp hdQL)))
        · refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQB2 ?_)
          calc B2G = ⁅B2G, B2G⁆ := hB2perf.symm
            _ ≤ ⁅QG ⊔ B2G, QG ⊔ B2G⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

end CFSG.StandardType.KGOm

end
