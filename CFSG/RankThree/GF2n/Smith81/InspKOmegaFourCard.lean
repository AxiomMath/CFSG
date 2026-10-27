module

public import CFSG.RankThree.GF2n.Smith81.InspKOmegaCard

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp.KFact

open Subgroup CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  CFSG.StandardType.RCSTOm CFSG.StandardType.KGOm CFSG.StandardType.RootCentOmega
  CFSG.RankThree.PartTwo.Sec21
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open scoped MatrixGroups commutatorElement

theorem centralizer_decomp_frame_core {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e) :
    Subgroup.centralizer {x} = (rootRadical Q P₁ P₂).comap σ ⊔
        ((leviFix (elementaryGroup Q) P₁ P₂).comap σ ⊔ (omFix Q P₁ P₂).comap σ) ∧
      (leviFix (elementaryGroup Q) P₁ P₂).comap σ ⊔ (omFix Q P₁ P₂).comap σ ≤
        Subgroup.normalizer ((rootRadical Q P₁ P₂).comap σ : Set U) ∧
      Disjoint ((rootRadical Q P₁ P₂).comap σ)
        ((leviFix (elementaryGroup Q) P₁ P₂).comap σ ⊔ (omFix Q P₁ P₂).comap σ) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite U := Finite.of_injective σ hσ
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
  refine ⟨hC, ?_, ?_⟩
  · rw [hRdef, hL₁def, hL₂def]
    exact sup_le (comap_le_normalizer (leviFix_le_normalizer_rootRadical h₁₂))
      (comap_le_normalizer (omFix_le_normalizer_rootRadical h₁₂))
  · rw [hRdef, hL₁def, hL₂def, Subgroup.disjoint_def]
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

theorem card_centralizer_dvd_of_frame_core {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {P₁ P₂ : HypPair Q} (hQ : (polarBilin Q).Nondegenerate)
    (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ) (hOE : orthDerived Q ≤ elementaryGroup Q)
    (h₁₂ : P₁.Orth P₂)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂))
      (CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub hQ h₁₂) ≤
      orthDerived (Q.restrict (wSub P₁ P₂)))
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e)
    {f N N₂ r r₂ : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : Odd r) (hr₂ : Odd r₂)
    (hU : Nat.card U = 2 ^ N * r)
    (hL₂ : Nat.card (orthDerived (Q.restrict (wSub P₁ P₂))) = 2 ^ N₂ * r₂) :
    Nat.card (Subgroup.centralizer ({x} : Set U)) ∣
      2 ^ (N - f - N₂) * Nat.card SL(2, K) *
        Nat.card (orthDerived (Q.restrict (wSub P₁ P₂))) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite U := Finite.of_injective σ hσ
  have hEich : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  obtain ⟨hC, hn, hd⟩ := centralizer_decomp_frame_core h₁₂ hσ hσE hx
  have hL₁E : leviFix (elementaryGroup Q) P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q P₁ P₂ ≤ σ.range := hσE ▸ fun g hg => (mem_omFix.mp hg).1
  have hR2 : IsPGroup 2 ((rootRadical Q P₁ P₂).comap σ) :=
    IsPGroup.comap_of_injective isPGroup_rootRadical σ hσ
  have hd12 : Disjoint ((leviFix (elementaryGroup Q) P₁ P₂).comap σ)
      ((omFix Q P₁ P₂).comap σ) := by
    rw [Subgroup.disjoint_def]
    intro y hy hy'
    apply hσ
    rw [map_one]
    exact Subgroup.disjoint_def.mp (disjoint_leviFix_omFix h₁₂) (Subgroup.mem_comap.mp hy)
      (Subgroup.mem_comap.mp hy')
  have h12 : (leviFix (elementaryGroup Q) P₁ P₂).comap σ ≤
      Subgroup.centralizer (((omFix Q P₁ P₂).comap σ) : Set U) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro h hh
    apply hσ
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp (leviFix_le_centralizer_omFix h₁₂ hg) (σ h) hh
  have hc1 : Nat.card ((leviFix (elementaryGroup Q) P₁ P₂).comap σ) = Nat.card SL(2, K) :=
    (card_comap_eq_of_le_range hσ hL₁E).trans
      (Nat.card_congr (leviFixEquiv P₁ P₂ h₁₂ hEich).toEquiv)
  have hc2 : Nat.card ((omFix Q P₁ P₂).comap σ) =
      Nat.card (orthDerived (Q.restrict (wSub P₁ P₂))) :=
    (card_comap_eq_of_le_range hσ hL₂E).trans
      (Nat.card_congr (omFixEquiv h₁₂ hQ hEΩ hOE
        (CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub hQ h₁₂) hΩ).toEquiv)
  have hSL : Nat.card SL(2, K) = 2 ^ f * (2 ^ (2 * f) - 1) := by
    rw [CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hK, ← pow_mul, mul_comm f 2]
  have hodd : Odd (2 ^ (2 * f) - 1) := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [show 2 * (g + 1) = (2 * g + 1) + 1 from by ring, pow_succ]
    exact ⟨2 ^ (2 * g + 1) - 1, by have := Nat.one_le_two_pow (n := 2 * g + 1); omega⟩
  have key := card_dvd_of_decomp (U := U) (x := x) (R := (rootRadical Q P₁ P₂).comap σ)
    (L₁ := (leviFix (elementaryGroup Q) P₁ P₂).comap σ) (L₂ := (omFix Q P₁ P₂).comap σ)
    hC hn hd hd12 h12 hR2 (N := N) (N₁ := f) (N₂ := N₂) hr hodd hr₂ hU
    (by rw [hc1, hSL]) (by rw [hc2, hL₂])
  rwa [hc1, hc2] at key

theorem card_centralizer_longRoot_plus_four_dvd {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hU : Nat.card (spinGroup (quadPlus 4 K)) = CFSG.Open.ordD 4 (2 ^ f)) :
    Nat.card (Subgroup.centralizer ({stdLongRootPlus K (by norm_num : 3 ≤ 4)} :
        Set (spinGroup (quadPlus 4 K)))) ∣
      (2 ^ f) ^ 9 * CFSG.Open.ordBC 1 (2 ^ f) * CFSG.Open.ordD 2 (2 ^ f) := by
  have hf1 : 1 ≤ f := by omega
  have hn3 : 3 ≤ 4 := by norm_num
  have h12 : (⟨1, by norm_num⟩ : Fin 4) ≠ ⟨2, by norm_num⟩ := by simp
  have hOE : orthDerived (quadPlus 4 K) ≤ elementaryGroup (quadPlus 4 K) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadPlus hn3]
  obtain ⟨r, hr, hUr⟩ := exists_ordD_eq (n := 4) (by norm_num) hf1
  obtain ⟨r₂, hr₂, hL₂r⟩ := exists_ordD_eq (n := 2) (by norm_num) hf1
  have hdimV : finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hplus := isPlusType_restrict_wSub_of_hypFrame (plusFrame 4 K hn3) hdimV h12 true true
    (one_ne_zero (α := K))
  have h₁₂ := orth₁₂ (plusFrame 4 K hn3) h12 true true (one_ne_zero (α := K))
  have hR := CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub
    (nondegenerate_polarBilin_quadPlus 4 K) h₁₂
  have hdimW : finrank K (wSub (framePair (plusFrame 4 K hn3) ⟨2, by norm_num⟩ true)
      (smulPair (framePair (plusFrame 4 K hn3) ⟨1, by norm_num⟩ true) (one_ne_zero (α := K)))) =
      2 * 2 := by
    have := finrank_wSub_add_four (Q := quadPlus 4 K) h₁₂
    omega
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨S, hS2, hS0⟩ := hplus
  have hΩ := omegaGroup_le_orthDerived_of_splitFour hR (by omega) ⟨S, by omega, hS0⟩ hq
  have hcard := card_orthDerived_plus_of_le (m := 2) (by norm_num) hK hR hdimW hΩ ⟨S, hS2, hS0⟩
  have key := card_centralizer_dvd_of_frame_core (nondegenerate_polarBilin_quadPlus 4 K)
    (CFSG.StandardType.RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn3) hOE h₁₂ hΩ
    CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus hn3)
    (CFSG.StandardType.RootCentOmega.spinAction_longRoot_eq_eichler (plusFrame 4 K hn3) h12 true
      true (1 : K)) hf1 hK hr hr₂ (hU.trans hUr) (hcard.trans hL₂r)
  rw [hcard, card_SL2_eq_ordBC hf1 hK] at key
  refine key.trans ?_
  have e : f * (4 * (4 - 1)) - f - f * (2 * (2 - 1)) = f * 9 := by omega
  rw [e, pow_mul]

theorem card_centralizer_longRoot_minus_four_dvd {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f)
    (hU : Nat.card (spinGroup (quadMinus 4 K b c)) = CFSG.Open.ordTwistedD 4 (2 ^ f)) :
    Nat.card (Subgroup.centralizer ({stdLongRootMinus K (by norm_num : 4 ≤ 4) b c} :
        Set (spinGroup (quadMinus 4 K b c)))) ∣
      (2 ^ f) ^ 9 * CFSG.Open.ordBC 1 (2 ^ f) * CFSG.Open.ordTwistedD 2 (2 ^ f) := by
  have hn4 : 4 ≤ 4 := le_rfl
  set F := (minusFrame 4 b c).toHypFrame with hF
  have h01 : (⟨0, by norm_num⟩ : Fin (4 - 1)) ≠ ⟨1, by norm_num⟩ := by simp
  have ha : (1 : K) ≠ 0 := one_ne_zero
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr
  have hEΩ := CFSG.StandardType.RootCentOmega.elementaryGroup_quadMinus_le_omegaGroup hirr hn4
  have hOE : orthDerived (quadMinus 4 K b c) ≤ elementaryGroup (quadMinus 4 K b c) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn4 hirr]
  obtain ⟨r, hr, hUr⟩ := exists_ordTwistedD_eq (n := 4) (by norm_num) hf
  obtain ⟨r₂, hr₂, hL₂r⟩ := exists_ordTwistedD_eq (n := 2) (by norm_num) hf
  have h₁₂ : (framePair F ⟨1, by norm_num⟩ true).Orth
      (smulPair (framePair F ⟨0, by norm_num⟩ true) ha) := orth₁₂ F h01 true true ha
  have hR := CFSG.StandardType.RCSTOm.nondegenerate_restrict_wSub hQ h₁₂
  have hdimW : finrank K (wSub (framePair F ⟨1, by norm_num⟩ true)
      (smulPair (framePair F ⟨0, by norm_num⟩ true) ha)) = 2 * 2 := by
    have h := finrank_wSub_add_four (Q := quadMinus 4 K b c) h₁₂
    rw [finrank_quadMinus (by norm_num)] at h
    omega
  have hts : ∀ U : Submodule K (wSub (framePair F ⟨1, by norm_num⟩ true)
      (smulPair (framePair F ⟨0, by norm_num⟩ true) ha)), finrank K U = 2 →
      ∃ u ∈ U, (quadMinus 4 K b c).restrict (wSub (framePair F ⟨1, by norm_num⟩ true)
        (smulPair (framePair F ⟨0, by norm_num⟩ true) ha)) u ≠ 0 :=
    fun U hU => exists_restrict_ne_zero_minus (by norm_num) hirr h₁₂ U hU
  have hneg : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType ((quadMinus 4 K b c).restrict
      (wSub (framePair F ⟨1, by norm_num⟩ true)
        (smulPair (framePair F ⟨0, by norm_num⟩ true) ha))) :=
    CFSG.StandardType.not_isPlusType_of_forall_ne_zero (d := 2) hdimW hts
  have hΩ := omegaGroup_le_orthDerived_of_four hR (by omega) hts
  have hcard := card_orthDerived_minus_of_le (m := 2) (by norm_num) hK hR hdimW hΩ hneg
  have hx := CFSG.StandardType.RootCentOmega.spinAction_longRoot_eq_eichler F h01 true true 1
  have key := card_centralizer_dvd_of_frame_core hQ hEΩ hOE h₁₂ hΩ
    (CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirr)
    (range_spinAction_quadMinus hn4 hirr) hx hf hK hr hr₂ (hU.trans hUr) (hcard.trans hL₂r)
  rw [hcard, card_SL2_eq_ordBC hf hK] at key
  refine key.trans ?_
  have e : f * (4 * (4 - 1)) - f - f * (2 * (2 - 1)) = f * 9 := by omega
  rw [e, pow_mul]

end CFSG.RankThree.GF2n.Smith81.Insp.KFact
