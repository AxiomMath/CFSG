module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmHyp
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmMinus
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSummand
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarking
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingOmega

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

theorem exists_kgPieces_frame {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {P₁ P₂ P₃ : HypPair Q}
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) {y₀ : V} (hy₀ : y₀ ≠ 0) (hy₀W : InW P₁ P₂ y₀)
    (hy₀3 : polar Q P₃.e y₀ = 0 ∧ polar Q P₃.f y₀ = 0)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂)) (RCSTOm.nondegenerate_restrict_wSub hQ h₁₂) ≤
      orthDerived (Q.restrict (wSub P₁ P₂)))
    (hWq : CFSG.IsQuasisimple (orthDerived (Q.restrict (wSub P₁ P₂))))
    (hWZ : Subgroup.center (orthDerived (Q.restrict (wSub P₁ P₂))) = ⊥)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e)
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) (u : U)
    {E : Subgroup G} (hE : E ≤ ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)}) :
    ∃ 𝒥 : Set (Subgroup G),
      (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)} →
        ⁅P, P⁆ = P → P ≤ sSup 𝒥) ∧
      ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)}) E J := by
  have hEichler : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  set φ := ψ.comp (MulAut.conj u).toMonoidHom with hφdef
  have hφ : Function.Injective φ := RCSTSp.comp_conj_injective hψ u
  have hφr : φ.range = ψ.range := RCSTSp.range_comp_conj ψ u
  have hr : ψ (u * x * u⁻¹) = φ x := by
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr, ← hφr] at hE ⊢
  have hRE : rootRadical Q P₁ P₂ ≤ σ.range := hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q P₁ P₂ ≤ σ.range := hσE ▸ fun g hg => (mem_omFix.mp hg).1
  set QG := Φ σ φ (rootRadical Q P₁ P₂) with hQGdef
  set AG := Φ σ φ (leviFix (elementaryGroup Q) P₁ P₂) with hAGdef
  set BG := Φ σ φ (omFix Q P₁ P₂) with hBGdef
  set C₀ : Subgroup G := φ.range ⊓ Subgroup.centralizer {φ x} with hC₀def
  have hC₀map : C₀ = (centralizer {x}).map φ := by
    rw [hC₀def, RCSTSp.range_inf_centralizer_of_injective hφ x]
  have hX : C₀ = QG ⊔ AG ⊔ BG := by
    rw [hC₀map, centralizer_eq_comap hσ hσE x, hx, centralizer_inf_elementaryGroup_eq h₁₂]
    change Φ σ φ _ = _
    rw [Φ_sup hσ φ (sup_le hRE hL₁E) hL₂E, Φ_sup hσ φ hRE hL₁E]
  have hQ2 : IsPGroup 2 QG := Φ_isPGroup φ hσ isPGroup_rootRadical
  have h1Q : AG ≤ Subgroup.normalizer (QG : Set G) :=
    Φ_le_normalizer φ (leviFix_le_normalizer_rootRadical h₁₂)
  have h2Q : BG ≤ Subgroup.normalizer (QG : Set G) :=
    Φ_le_normalizer φ (omFix_le_normalizer_rootRadical h₁₂)
  have h12 : AG ≤ Subgroup.centralizer (BG : Set G) :=
    Φ_le_centralizer hσ φ (leviFix_le_centralizer_omFix h₁₂)
  have hBA : BG ≤ Subgroup.centralizer (AG : Set G) := Subgroup.le_centralizer_iff.mp h12
  have eB : ↥BG ≃* ↥(orthDerived (Q.restrict (wSub P₁ P₂))) :=
    (Φ_equiv hσ φ hφ hL₂E).trans
      (omFixEquiv h₁₂ hQ hEΩ hOE (RCSTOm.nondegenerate_restrict_wSub hQ h₁₂) hΩ)
  have hBq : CFSG.IsQuasisimple BG := CFSG.LocalCores.isQuasisimple_of_mulEquiv eB.symm hWq
  have hBZ : Subgroup.center BG = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eB.symm, hWZ,
      Subgroup.map_bot]
  have hSB : GGRCSOmSummand BG := ggRCSOmSummand_of_isQuasisimple hBq hBZ
  obtain ⟨x', hx'W, hx'3, hy₀x'⟩ :=
    exists_polar_eq_one_perp hQ h₁₂ h₁₃ h₂₃ hy₀ hy₀W hy₀3
  have hQB : QG ≤ ⁅QG ⊔ BG, QG ⊔ BG⁆ := by
    have h := Φ_mono (σ := σ) φ
      (rootRadical_le_commutator_omFix h₁₂ h₁₃ h₂₃ hy₀W hx'W hy₀3 hx'3 hy₀x')
    rwa [Φ_commutator hσ φ (sup_le hRE hL₂E) (sup_le hRE hL₂E), Φ_sup hσ φ hRE hL₂E] at h
  have hX₃ : C₀ = QG ⊔ (AG ⊔ BG ⊔ ⊥) := by
    rw [hX, sup_bot_eq, sup_assoc]
  have eA : ↥AG ≃* SL(2, K) := (Φ_equiv hσ φ hφ hL₁E).trans (leviFixEquiv P₁ P₂ h₁₂ hEichler)
  have hdisj := Φ_disjoint hσ φ hφ (disjoint_rootRadical_sup h₁₂)
  rw [Φ_sup hσ φ hL₁E hL₂E] at hdisj
  have hperfB : ⁅QG ⊔ BG, QG ⊔ BG⁆ = QG ⊔ BG := by
    refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQB ?_)
    calc BG = ⁅BG, BG⁆ := (Subgroup.isPerfect_iff.mp hBq.1).symm
      _ ≤ ⁅QG ⊔ BG, QG ⊔ BG⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  obtain ⟨hBqA, hBm⟩ := isQuasisimple_largeEvenMarking_of_equiv_orthDerived
    (RCSTOm.nondegenerate_restrict_wSub hQ h₁₂) hWq eB
  have hpB (hO2 : pCoreOf 2 C₀ = QG) : GGRCSKGPiece C₀ E (QG ⊔ BG) :=
    ggRCSKGPiece_of_summand (Q := QG) (L := BG) (M := AG)
      (by rw [hX, sup_assoc, sup_comm AG BG]) hO2 h2Q h1Q hBA
      (disjoint_iff.mp (hdisj.mono_right le_sup_right)) hperfB hBqA hBm hE
  rcases card_eq_two_or_four_le K with hK | hK
  ·
    obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
    have eS : ↥AG ≃* Equiv.Perm (Fin 3) := eA.trans e3
    have hSs : Group.IsSolvable ↥AG := by
      have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
      exact Group.isSolvable_of_isSolvable_injective (f := eS.toMonoidHom) eS.injective
    have hO2 : pCoreOf 2 C₀ = QG :=
      pCoreOf_eq_of_three_summands hX₃ hQ2 h1Q h2Q bot_le h12 (le_centralizer_bot _)
        (le_centralizer_bot _) (ggRCSOmSummand_of_perm eS) hSB ggRCSOmSummand_bot
    have hD : CFSG.Quasithin.perfectCore C₀ = QG ⊔ BG :=
      perfectCore_eq_of_solvable (by rw [hX, sup_assoc])
        (le_normalizer_sup_of_centralizer h1Q h12) hSs hperfB
    refine ⟨{QG ⊔ BG}, ?_, ?_⟩
    · intro P hP hPperf
      rw [sSup_singleton]
      exact (CFSG.Quasithin.le_perfectCore_of_perfect hP hPperf).trans (le_of_eq hD)
    · intro J hJ
      rw [Set.mem_singleton_iff] at hJ
      subst hJ
      exact hpB hO2
  ·
    letI : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
    have hKnat : Nat.card K = 2 ^ (f : ℕ) := by
      rw [Nat.card_eq_fintype_card, hKf]
    have hf2 : 2 ≤ (f : ℕ) := by
      have h4 : 4 ≤ 2 ^ (f : ℕ) := hKnat ▸ hK
      by_contra h
      push Not at h
      have hle : 2 ^ (f : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_one] at hle
      omega
    obtain ⟨hAqA, hAm⟩ := isQuasisimple_largeEvenMarking_of_equiv_SL2 hKnat hf2 eA
    have hAq : CFSG.IsQuasisimple ↥AG := CFSG.LocalCores.isQuasisimple_of_mulEquiv eA.symm
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK))
    have hAZ : Subgroup.center ↥AG = ⊥ := by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eA.symm,
        center_SL2_eq_bot_of_charTwo, Subgroup.map_bot]
    have hQA : QG ≤ ⁅QG ⊔ AG, QG ⊔ AG⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_leviFix h₁₂ h₁₃ h₂₃)
      rwa [Φ_commutator hσ φ (sup_le hRE hL₁E) (sup_le hRE hL₁E), Φ_sup hσ φ hRE hL₁E] at h
    have hO2 : pCoreOf 2 C₀ = QG :=
      pCoreOf_eq_of_three_summands hX₃ hQ2 h1Q h2Q bot_le h12 (le_centralizer_bot _)
        (le_centralizer_bot _) (ggRCSOmSummand_of_isQuasisimple hAq hAZ) hSB
        ggRCSOmSummand_bot
    have hperfA : ⁅QG ⊔ AG, QG ⊔ AG⁆ = QG ⊔ AG := by
      refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQA ?_)
      calc AG = ⁅AG, AG⁆ := (Subgroup.isPerfect_iff.mp hAq.1).symm
        _ ≤ ⁅QG ⊔ AG, QG ⊔ AG⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
    have hpA : GGRCSKGPiece C₀ E (QG ⊔ AG) :=
      ggRCSKGPiece_of_summand (Q := QG) (L := AG) (M := BG)
        (by rw [hX, sup_assoc]) hO2 h1Q h2Q h12
        (disjoint_iff.mp (hdisj.mono_right le_sup_left)) hperfA hAqA hAm hE
    refine ⟨{QG ⊔ AG, QG ⊔ BG}, ?_, ?_⟩
    · intro P hP _
      refine hP.trans ?_
      calc C₀ = QG ⊔ AG ⊔ BG := hX
        _ ≤ (QG ⊔ AG) ⊔ (QG ⊔ BG) :=
          sup_le le_sup_left ((le_sup_right : BG ≤ QG ⊔ BG).trans le_sup_right)
        _ = sSup ({QG ⊔ AG, QG ⊔ BG} : Set (Subgroup G)) := by rw [sSup_pair]
    · intro J hJ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJ
      rcases hJ with rfl | rfl
      · exact hpA
      · exact hpB hO2

theorem exists_kgPieces_hypFrame_five {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {N : ℕ}
    (F : HypFrame Q N) (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    {i j k l m : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m) (hjk : j ≠ k)
    (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) (s t : Bool) {c : K}
    (hc : c ≠ 0) {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U}
    (hx : σ x = eichler Q (F.vec j t) (c • F.vec i s))
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) (u : U)
    {E : Subgroup G} (hE : E ≤ ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)}) :
    ∃ 𝒥 : Set (Subgroup G),
      (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)} →
        ⁅P, P⁆ = P → P ≤ sSup 𝒥) ∧
      ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)}) E J := by
  have h₁₂ := orth₁₂ F hij s t hc
  have hR := RCSTOm.nondegenerate_restrict_wSub hQ h₁₂
  have hT := exists_totallySingular_wSub F hik hil him hjk hjl hjm hkl hkm hlm s t hc
  exact exists_kgPieces_frame (P₃ := framePair F l true) hQ hEΩ hOE h₁₂
    (orth₁₃ F hjl t true) (orth₂₃ F hil s true hc) (y₀ := F.vec k true)
    (framePair F k true).e_ne_zero
    (inW_frame F hc (fun v => F.polar_vec_of_ne hik v true)
      (fun v => F.polar_vec_of_ne hjk v true))
    ⟨F.polar_vec_of_ne hkl.symm true true, F.polar_vec_of_ne hkl.symm false true⟩
    (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT)
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)
    (center_orthDerived_eq_bot' hR hT (exists_restrict_ne_zero F hik hjk hc))
    hσ hσE hx ψ hψ u hE

theorem exists_kgPieces_minus_small {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hn4 : 4 ≤ n) (hn5 : n ≤ 5) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) {a : K} (ha : a ≠ 0)
    {G : Type} [Group G] [Finite G] (ψ : spinGroup (quadMinus n K b c) →* G)
    (hψ : Function.Injective ψ) (u : spinGroup (quadMinus n K b c)) {E : Subgroup G}
    (hE : E ≤ ψ.range ⊓ Subgroup.centralizer
      {ψ (u * (minusFrame n b c).longRoot hij s t (.ofAdd a) * u⁻¹)}) :
    ∃ 𝒥 : Set (Subgroup G),
      (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer
          {ψ (u * (minusFrame n b c).longRoot hij s t (.ofAdd a) * u⁻¹)} →
        ⁅P, P⁆ = P → P ≤ sSup 𝒥) ∧
      ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer
        {ψ (u * (minusFrame n b c).longRoot hij s t (.ofAdd a) * u⁻¹)}) E J := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have h₁₂ := orth₁₂ (minusFrame n b c).toHypFrame hij s t ha
  have hR := RCSTOm.nondegenerate_restrict_wSub hQ h₁₂
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
    obtain ⟨hWq, hWZ, _⟩ := isQuasisimple_orthDerived_of_four hR hdim hts
    have hΩ := omegaGroup_le_orthDerived_of_four hR hdim hts
    exact exists_kgPieces_frame (P₃ := framePair (minusFrame 4 b c).toHypFrame k true) hQ hEΩ
      hOE h₁₂ (orth₁₃ _ hjk t true) (orth₂₃ _ hik s true ha) hz0 hzW ⟨hz k true, hz k false⟩
      hΩ hWq hWZ (spinAction_quadMinus_injective hirr)
      (range_spinAction_quadMinus hn4 hirr) hσx ψ hψ u hE
  ·
    have hdim : finrank K (wSub (framePair (minusFrame 5 b c).toHypFrame j t)
        (smulPair (framePair (minusFrame 5 b c).toHypFrame i s) ha)) = 6 := by
      rw [hdimW]
    obtain ⟨hWq, hWZ⟩ := isQuasisimple_orthDerived_of_six hR hdim hts
    have hΩ := omegaGroup_le_orthDerived_of_six hR hdim hts
    exact exists_kgPieces_frame (P₃ := framePair (minusFrame 5 b c).toHypFrame k true) hQ hEΩ
      hOE h₁₂ (orth₁₃ _ hjk t true) (orth₂₃ _ hik s true ha) hz0 hzW ⟨hz k true, hz k false⟩
      hΩ hWq hWZ (spinAction_quadMinus_injective hirr)
      (range_spinAction_quadMinus hn4 hirr) hσx ψ hψ u hE

end CFSG.StandardType.KGOm

end
