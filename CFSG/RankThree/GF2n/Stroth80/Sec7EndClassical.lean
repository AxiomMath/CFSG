module

public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAOmega

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement
open CFSG.LieType.Universal.Spin (quadMinus)

section OmegaPlus

private theorem endgJ_card_plus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 3 ≤ m) :
    (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadPlus_eq_map hm,
    Subgroup.card_map_of_injective (MulEquiv.injective _)]
  exact CFSG.SeitzReduction.OmegaPilot.card_elementaryGroup_quadPlus_of_three_le hm

private theorem endgJ_two_dvd_card (K : Type) [Field K] [Finite K] [CharP K 2] :
    2 ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 (PNat.ne_zero n)

theorem endg_omegaPlus_facts {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {m : ℕ} (hm : 3 ≤ m) :
    IsSimpleGroup ↥(StatedOmega (StatedQuadPlus m K)) ∧
      16 ∣ Nat.card ↥(StatedOmega (StatedQuadPlus m K)) ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card K ^ 2 + 1 →
        p ∣ Nat.card ↥(StatedOmega (StatedQuadPlus m K)) := by
  have hcenter : Subgroup.center ↥(StatedOmega (StatedQuadPlus m K)) = ⊥ :=
    (CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (K := K) hm).trans
      (CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
        (K := K) (n := m) (by omega))
  have hq := statedOmega_plus_quasisimple_of_three_le K m hm
  have hS : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus m K)) := by
    obtain ⟨-, hSQ, -⟩ := hq
    exact (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hcenter.symm)).isSimpleGroup
  have hord := endgJ_card_plus (K := K) hm
  have h2Z : (2 : ℤ) ∣ (Nat.card K : ℤ) := by
    exact_mod_cast endgJ_two_dvd_card K
  have h2m : 2 ≤ m - 1 := by omega
  have h4 : 4 ≤ m * (m - 1) := (by norm_num : 4 ≤ 3 * 2).trans (Nat.mul_le_mul hm h2m)
  have h16 : (16 : ℤ) ∣ (Nat.card K : ℤ) ^ (m * (m - 1)) := by
    have h1 : (2 : ℤ) ^ 4 ∣ (Nat.card K : ℤ) ^ 4 := pow_dvd_pow_of_dvd h2Z 4
    have h2' : (Nat.card K : ℤ) ^ 4 ∣ (Nat.card K : ℤ) ^ (m * (m - 1)) :=
      pow_dvd_pow _ h4
    have h16eq : (16 : ℤ) = 2 ^ 4 := by norm_num
    rw [h16eq]
    exact h1.trans h2'
  refine ⟨hS, ?_, ?_⟩
  · have hdiv : (16 : ℤ) ∣ (Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℤ) := by
      rw [hord]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h16 _) _
    exact_mod_cast hdiv
  · intro p hp hpd
    have hpZ : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by
      have h := Int.natCast_dvd_natCast.mpr hpd
      push_cast at h
      exact h
    have hfac : (Nat.card K : ℤ) ^ 2 + 1 ∣ (Nat.card K : ℤ) ^ (2 * 2) - 1 :=
      ⟨(Nat.card K : ℤ) ^ 2 - 1, by ring⟩
    have hmem : (2 : ℕ) ∈ Finset.Icc 1 (m - 1) := Finset.mem_Icc.mpr ⟨by norm_num, h2m⟩
    have hP : (Nat.card K : ℤ) ^ (2 * 2) - 1 ∣
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
      Finset.dvd_prod_of_mem (fun i : ℕ => (Nat.card K : ℤ) ^ (2 * i) - 1) hmem
    have hdivZ : (p : ℤ) ∣ (Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℤ) := by
      rw [hord]
      exact dvd_mul_of_dvd_right (hpZ.trans (hfac.trans hP)) _
    exact_mod_cast hdivZ

end OmegaPlus

section OmegaMinus

private theorem endgK_card_ge_four {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 4 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map hm hirr,
    Subgroup.card_map_of_injective (MulEquiv.injective _)]
  exact CFSG.Timmesfeld.ClassicalOrders.card_elementaryGroup_quadMinus hm hirr

private theorem endgK_card_orth {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hd : 2 * n = 4 ∨ 2 * n = 6) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)) =
      2 * Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆ := by
  have hmin := CFSG.ClassicalGroups.Orthogonal.isMinus_quadMinus (K := K) (m := n)
    (by omega) hirr
  obtain ⟨-, -, -, hidx, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (quadMinus n K b c) hmin.nondeg (by rw [hmin.finrank_eq]; exact hd)
      (fun U hU => hmin.noTS U (by rw [hmin.finrank_eq] at hU; omega))
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hcard := ((⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)⁆).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcard
  omega

private theorem endgK_card_two {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ (2 * (2 - 1)) * ((Nat.card K : ℤ) ^ 2 + 1) *
        ∏ i ∈ Finset.Icc 1 (2 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map_of_two_le (n := 2)
      (by norm_num) hirr, Subgroup.card_map_of_injective (MulEquiv.injective _),
    ← CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
      (n := 2) (by norm_num) hirr]
  have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
      2 * (Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)⁆ : ℤ) := by
    exact_mod_cast endgK_card_orth (n := 2) (Or.inl (by norm_num)) hirr
  have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (2 * (2 - 1)) * ((Nat.card K : ℤ) ^ 2 + 1) *
        ∏ i ∈ Finset.Icc 1 (2 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus 1 hirr).2
  linarith

private theorem endgK_card_three {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
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
    exact_mod_cast endgK_card_orth (n := 3) (Or.inr (by norm_num)) hirr
  have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (3 * (3 - 1)) * ((Nat.card K : ℤ) ^ 3 + 1) *
        ∏ i ∈ Finset.Icc 1 (3 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
    (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus 2 hirr).2
  linarith

private theorem endgK_card {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | h4
  · exact endgK_card_two hirr
  · exact endgK_card_three hirr
  · exact endgK_card_ge_four h4 hirr

private theorem endgK_card_eq_two_pow (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ f : ℕ, Nat.card K = 2 ^ f := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨(n : ℕ), by rw [Nat.card_eq_fintype_card, hn]⟩

private theorem endgK_four_dvd (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) : 4 ∣ Nat.card K := by
  obtain ⟨f, hf⟩ := endgK_card_eq_two_pow K
  rw [hf] at hK ⊢
  rcases f with _ | _ | f
  · norm_num at hK
  · norm_num at hK
  · exact ⟨2 ^ f, by ring⟩

private theorem endgK_sixteen_dvd_pow (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {e : ℕ} (he : 2 ≤ e) :
    (16 : ℤ) ∣ (Nat.card K : ℤ) ^ e := by
  obtain ⟨t, ht⟩ := endgK_four_dvd K hK
  have h4 : (Nat.card K : ℤ) = 4 * (t : ℤ) := by exact_mod_cast ht
  have h2 : (16 : ℤ) ∣ (Nat.card K : ℤ) ^ 2 := ⟨(t : ℤ) ^ 2, by rw [h4]; ring⟩
  exact dvd_trans h2 (pow_dvd_pow _ he)

private theorem endgK_two_le_mul {m : ℕ} (hm : 2 ≤ m) : 2 ≤ m * (m - 1) := by
  have h1 : 1 ≤ m - 1 := by omega
  calc (2 : ℕ) = 2 * 1 := rfl
    _ ≤ m * (m - 1) := Nat.mul_le_mul hm h1

private theorem endgK_sixteen_dvd_order {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {m : ℕ} (hm : 2 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (16 : ℤ) ∣ (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K b c)) : ℤ) := by
  rw [endgK_card hm hirr]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (endgK_sixteen_dvd_pow K hK (endgK_two_le_mul hm)) _) _

private theorem endgK_sq_add_one_dvd {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((Nat.card K : ℤ) ^ 2 + 1) ∣
      (Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus m K b c)) : ℤ) := by
  rw [endgK_card hm hirr]
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_refl _) _) _
  · have hmem : 2 ∈ Finset.Icc 1 (m - 1) := Finset.mem_Icc.mpr ⟨by norm_num, by omega⟩
    have hf : ((Nat.card K : ℤ) ^ 2 + 1) ∣ (Nat.card K : ℤ) ^ (2 * 2) - 1 :=
      ⟨(Nat.card K : ℤ) ^ 2 - 1, by ring⟩
    have hP : ((Nat.card K : ℤ) ^ 2 + 1) ∣
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
      dvd_trans hf (Finset.dvd_prod_of_mem (fun i => (Nat.card K : ℤ) ^ (2 * i) - 1) hmem)
    exact dvd_mul_of_dvd_right hP _

theorem endg_omegaMinus_facts {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {m : ℕ} (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup ↥(StatedOmega (StatedQuadMinus m K b c)) ∧
      16 ∣ Nat.card ↥(StatedOmega (StatedQuadMinus m K b c)) ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card K ^ 2 + 1 →
        p ∣ Nat.card ↥(StatedOmega (StatedQuadMinus m K b c)) := by
  refine ⟨?_, ?_, ?_⟩
  · open CFSG.ComponentClassification.RankTwoClassical in
      exact ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le hm hirr
  · apply Int.natCast_dvd_natCast.mp
    exact_mod_cast endgK_sixteen_dvd_order hK hm hirr
  · intro p _ hpd
    have hp' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by
      have h := Int.natCast_dvd_natCast.mpr hpd
      push_cast at h
      exact h
    exact Int.natCast_dvd_natCast.mp (dvd_trans hp' (endgK_sq_add_one_dvd hm hirr))

end OmegaMinus

section SymplecticEndgame

private theorem endgQ_two_dvd_card (K : Type) [Field K] [Finite K] [CharP K 2] :
    2 ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 (PNat.ne_zero n)

theorem endg_sp_facts {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {m : ℕ} (hm : 2 ≤ m) :
    IsSimpleGroup ↥(StatedSp m K) ∧ 16 ∣ Nat.card ↥(StatedSp m K) ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card K ^ 2 + 1 → p ∣ Nat.card ↥(StatedSp m K) := by
  have hcenter : Subgroup.center ↥(StatedSp m K) = ⊥ :=
    CFSG.HardMathSupport.Dickson.Bal207.center_statedSp_eq_bot_of_charP_two (K := K) m
  have hq := statedSp_quasisimple_of_card m K (by omega) hK
  have hS : IsSimpleGroup ↥(StatedSp m K) := by
    obtain ⟨-, hSQ, -⟩ := hq
    exact (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hcenter.symm)).isSimpleGroup
  have hord := CFSG.GroupTheory.WeirSylow.natCard_statedSp_cast K m
  have h2Z : (2 : ℤ) ∣ (Nat.card K : ℤ) := by
    exact_mod_cast endgQ_two_dvd_card K
  have h4 : 4 ≤ m ^ 2 := by nlinarith
  have h16 : (16 : ℤ) ∣ (Nat.card K : ℤ) ^ (m ^ 2) := by
    have h1 : (2 : ℤ) ^ 4 ∣ (Nat.card K : ℤ) ^ 4 := pow_dvd_pow_of_dvd h2Z 4
    have h2' : (Nat.card K : ℤ) ^ 4 ∣ (Nat.card K : ℤ) ^ (m ^ 2) :=
      pow_dvd_pow _ h4
    have h16eq : (16 : ℤ) = 2 ^ 4 := by norm_num
    rw [h16eq]
    exact h1.trans h2'
  refine ⟨hS, ?_, ?_⟩
  · have hdiv : (16 : ℤ) ∣ (Nat.card ↥(StatedSp m K) : ℤ) := by
      rw [hord]
      exact dvd_mul_of_dvd_left h16 _
    exact_mod_cast hdiv
  · intro p hp hpd
    have hpZ : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by
      have h := Int.natCast_dvd_natCast.mpr hpd
      push_cast at h
      exact h
    have hfac : (Nat.card K : ℤ) ^ 2 + 1 ∣ ((Nat.card K : ℤ) ^ 2) ^ 2 - 1 :=
      ⟨(Nat.card K : ℤ) ^ 2 - 1, by ring⟩
    have hmem : (2 : ℕ) ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨by norm_num, hm⟩
    have hP : ((Nat.card K : ℤ) ^ 2) ^ 2 - 1 ∣
        ∏ j ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ j - 1) :=
      Finset.dvd_prod_of_mem (fun j : ℕ => ((Nat.card K : ℤ) ^ 2) ^ j - 1) hmem
    have hdivZ : (p : ℤ) ∣ (Nat.card ↥(StatedSp m K) : ℤ) := by
      rw [hord]
      exact dvd_mul_of_dvd_right (hpZ.trans (hfac.trans hP)) _
    exact_mod_cast hdivZ

end SymplecticEndgame

end CFSG.RankThree.GF2n.Stroth80
