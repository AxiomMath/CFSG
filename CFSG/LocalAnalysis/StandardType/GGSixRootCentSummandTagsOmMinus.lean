module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmHyp
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmega
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEightBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic

public section

namespace CFSG.StandardType

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)

namespace RCSTOm

section Minus

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

omit [Finite K] [CharP K 2] in
theorem finrank_quadMinus (hn : 1 ≤ n) :
    finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

omit [CharP K 2] in
theorem exists_restrict_ne_zero_minus (hn : 2 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {P₁ P₂ : HypPair (quadMinus n K b c)} (h₁₂ : P₁.Orth P₂)
    (U : Submodule K (wSub P₁ P₂)) (hU : finrank K U = n - 2) :
    ∃ u ∈ U, (quadMinus n K b c).restrict (wSub P₁ P₂) u ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨T', hT'd, hT'⟩ := exists_totallySingular_add_two h₁₂ U h
  apply CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by omega : 1 ≤ n) hirr
  refine ⟨T', ?_, hT'⟩
  rw [hT'd, hU, finrank_quadMinus (by omega)]
  omega

theorem ggRCSLayer_minus_small {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn4 : 4 ≤ n) (hn5 : n ≤ 5)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    {a : K} (ha : a ≠ 0) {G : Type} [Group G] [Finite G] (ψ : spinGroup (quadMinus n K b c) →* G)
    (hψ : Function.Injective ψ) {M : Subgroup G} (hG₀M : ψ.range ≤ M)
    (hM : M ≤ normalizer (ψ.range : Set G)) (u : spinGroup (quadMinus n K b c)) :
    GGRCSLayer p ψ.range M (ψ (u * (minusFrame n b c).longRoot hij s t (.ofAdd a) * u⁻¹)) := by
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
    refine ggRCSLayer_frame (P₃ := framePair (minusFrame 4 b c).toHypFrame k true) hp hp2 hQ hEΩ
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
    exact ggRCSLayer_frame (P₃ := framePair (minusFrame 5 b c).toHypFrame k true) hp hp2 hQ hEΩ
      hOE h₁₂ (orth₁₃ _ hjk t true) (orth₂₃ _ hik s true ha) hz0 hzW ⟨hz k true, hz k false⟩
      hΩ hWq hWZ (fun hK _ => three_dvd_card_omFix _ hik' hil' hjk' hjl' hkl' s t ha hK)
      (spinAction_quadMinus_injective hirr) (range_spinAction_quadMinus hn4 hirr) hσx hxC ψ hψ
      hG₀M hM u

end Minus

end RCSTOm

section Tag

theorem ggRootCentLayerTag_POmegaMinus : GGRootCentLayerTag .POmegaMinus := by
  intro G _ _ p n f ψ hp hp2 hadm _ hker hC _ r hr
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
  · exact RCSTOm.ggRCSLayer_minus_small hp hp2 hn hn5 hirr hij s t ha ψ hinj
      Subgroup.le_normalizer le_rfl u
  · obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
      RCSTOm.exists_three_ne (by omega : 5 ≤ n - 1) i j
    refine RCSTOm.ggRCSLayer_hypFrame_five _ hp hp2
      (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) hirr)
      (elementaryGroup_quadMinus_le_omegaGroup hirr hn) ?_ hij hik hil him hjk hjl hjm hkl hkm
      hlm s t ha (spinAction_quadMinus_injective hirr) (range_spinAction_quadMinus hn hirr)
      (spinAction_longRoot_eq_eichler _ hij s t a)
      (centralizer_longRoot_minus_le hirr hn hij s t ha) ψ hinj Subgroup.le_normalizer le_rfl u
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn hirr]

end Tag

end CFSG.StandardType
