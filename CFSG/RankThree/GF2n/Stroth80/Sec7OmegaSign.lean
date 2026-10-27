module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAOmega

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.LieType.Universal.Spin (quadMinus)
open scoped commutatorElement

private theorem omegaSign_range_equiv {R H₁ H₂ : Type} [Group R] [Group H₁] [Group H₂]
    (φ₁ : R →* H₁) (φ₂ : R →* H₂) (h : φ₁.ker = φ₂.ker) :
    Nonempty (φ₁.range ≃* φ₂.range) :=
  ⟨((QuotientGroup.quotientKerEquivRange φ₁).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h)).trans (QuotientGroup.quotientKerEquivRange φ₂)⟩

private theorem omegaSign_charP_two {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

private theorem omegaSign_card_plus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 3 ≤ m) :
    (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadPlus_eq_map hm,
    Subgroup.card_map_of_injective (MulEquiv.injective _)]
  exact CFSG.SeitzReduction.OmegaPilot.card_elementaryGroup_quadPlus_of_three_le hm

private theorem omegaSign_card_minus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 4 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map hm hirr,
    Subgroup.card_map_of_injective (MulEquiv.injective _)]
  exact CFSG.Timmesfeld.ClassicalOrders.card_elementaryGroup_quadMinus hm hirr

private theorem omegaSign_ne {q : ℤ} (hq : 1 < q) (m : ℕ) {P : ℤ} (hP : 0 < P) :
    q ^ (m * (m - 1)) * (q ^ m - 1) * P ≠ q ^ (m * (m - 1)) * (q ^ m + 1) * P := by
  intro h
  have hX : 0 < q ^ (m * (m - 1)) := pow_pos (by omega) _
  have h2 : q ^ (m * (m - 1)) * P * 2 = 0 := by linear_combination (-1 : ℤ) * h
  have h3 : 0 < q ^ (m * (m - 1)) * P * 2 := mul_pos (mul_pos hX hP) two_pos
  linarith

private theorem omegaSign_prod_pos {q : ℤ} (hq : 1 < q) (m : ℕ) :
    0 < ∏ i ∈ Finset.Icc 1 (m - 1), (q ^ (2 * i) - 1) := by
  apply Finset.prod_pos
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have h1 : 1 < q ^ (2 * i) := one_lt_pow₀ hq (by omega)
  linarith

private theorem omegaSign_not_simple_prod (A : Type) [Group A] :
    ¬ IsSimpleGroup (A × A) := by
  intro h
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact not_nontrivial (A × A) h.toNontrivial
  · obtain ⟨a, ha⟩ := exists_ne (1 : A)
    rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.snd A A).ker with h1 | h1
    · have hmem : ((a, 1) : A × A) ∈ (MonoidHom.snd A A).ker := MonoidHom.mem_ker.mpr rfl
      rw [h1, Subgroup.mem_bot] at hmem
      exact ha (congrArg Prod.fst hmem)
    · have hmem : ((1, a) : A × A) ∈ (MonoidHom.snd A A).ker := by
        rw [h1]
        exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hmem
      exact ha (by simpa using hmem)

private theorem omegaSign_card_orth_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)) =
      2 * Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆ := by
  have hmin := CFSG.ClassicalGroups.Orthogonal.isMinus_quadMinus (K := K) (m := 3)
    (by norm_num) hirr
  obtain ⟨-, -, -, hidx, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (quadMinus 3 K b c) hmin.nondeg (Or.inr (by rw [hmin.finrank_eq]))
      (fun U hU => hmin.noTS U (by rw [hmin.finrank_eq] at hU; omega))
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c) := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hcard := ((⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c))).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcard
  omega

private theorem omegaSign_card_minus_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ (3 * (3 - 1)) * ((Nat.card K : ℤ) ^ 3 + 1) *
        ∏ i ∈ Finset.Icc 1 (3 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map_of_two_le (n := 3)
      (by norm_num) hirr, Subgroup.card_map_of_injective (MulEquiv.injective _),
    ← CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
      (n := 3) (by norm_num) hirr]
  have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)) : ℤ) =
      2 * (Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)⁆ : ℤ) := by
    exact_mod_cast omegaSign_card_orth_three hirr
  have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (3 * (3 - 1)) * ((Nat.card K : ℤ) ^ 3 + 1) *
        ∏ i ∈ Finset.Icc 1 (3 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus 2 hirr).2
  linarith

theorem omegaSignStatement_holds : OmegaSignStatement := by
  intro G _ _ M Q Z B hc t m hm hP hM
  obtain ⟨n, k, hZn, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq1 : (1 : ℤ) < (Nat.card Z : ℤ) := by omega
  obtain ⟨K₁, hK₁, hfin₁, hcard₁, φ₁, hr₁, hk₁, -⟩ := hP
  obtain ⟨K₂, hK₂, hfin₂, hcard₂, b, c, hirr, φ₂, hr₂, hk₂, -⟩ := hM
  have hchar₁ : CharP K₁ 2 := omegaSign_charP_two (f := n) (hcard₁.trans hZn)
  have hchar₂ : CharP K₂ 2 := omegaSign_charP_two (f := n) (hcard₂.trans hZn)
  obtain ⟨e0⟩ := omegaSign_range_equiv φ₁ φ₂ (hk₁.trans hk₂.symm)
  have e : ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K₁)) ≃*
      ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K₂ b c)) :=
    (MulEquiv.subgroupCongr hr₁).symm.trans (e0.trans (MulEquiv.subgroupCongr hr₂))
  have hcardEq : Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K₁)) =
      Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K₂ b c)) :=
    Nat.card_congr e.toEquiv
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · have h4K₁ : 4 ≤ Nat.card K₁ := by
      rw [hcard₁]
      exact hq4
    obtain ⟨eP⟩ := CFSG.RankThree.GF2n.Stroth80.statedOmega_plus_four_nonempty_equiv K₁ h4K₁
    open CFSG.ComponentClassification.RankTwoClassical in
    haveI hSM : IsSimpleGroup ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K₂ b c)) :=
      ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le (le_refl 2) hirr
    haveI hSP : IsSimpleGroup ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 2 K₁)) :=
      e.isSimpleGroup
    exact omegaSign_not_simple_prod _ eP.symm.isSimpleGroup
  · have hPlus := omegaSign_card_plus (K := K₁) hm3
    rw [hcard₁] at hPlus
    have hMinus : (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K₂ b c)) : ℤ) =
        (Nat.card Z : ℤ) ^ (m * (m - 1)) * ((Nat.card Z : ℤ) ^ m + 1) *
          ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card Z : ℤ) ^ (2 * i) - 1) := by
      rcases (show m = 3 ∨ 4 ≤ m by omega) with rfl | hm4
      · rw [omegaSign_card_minus_three hirr, hcard₂]
      · rw [omegaSign_card_minus hm4 hirr, hcard₂]
    have hEq : (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K₁)) : ℤ) =
        (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K₂ b c)) : ℤ) := by
      rw [hcardEq]
    rw [hPlus, hMinus] at hEq
    exact omegaSign_ne hq1 m (omegaSign_prod_pos hq1 m) hEq

end CFSG.RankThree.GF2n.Stroth80
