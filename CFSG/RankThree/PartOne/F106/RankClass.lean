module

public import CFSG.RankThree.PartOne.BRANCH.RankClassical

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143X
  CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartOne.BRANCH

theorem false_of_statedProj_det_five {n : ℕ} (hn2 : 2 ≤ n) (hn5 : n ≤ 5) {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL (Fin n) K))
    (hdet : ∀ g ∈ M, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) {T : Type} [Group T]
    (e : T ≃* StatedProj M) {q : ℕ} (hq : q.Prime) (hq37 : q = 3 ∨ q = 7) (hqK : (q : K) ≠ 0)
    (hnK : n % 2 = 1 → (n : K) ≠ 0) {D : Subgroup T} (hD : IsElementaryAbelian q D)
    (hcard : Nat.card D = q ^ 5) : False := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hqn : q ∣ n
  · have h3 : q = 3 ∧ n = 3 := by
      rcases hq37 with rfl | rfl
      · exact ⟨rfl, by omega⟩
      · omega
    obtain ⟨rfl, rfl⟩ := h3
    have hb := card_le_of_statedProj hq hqK (hnK rfl) M hdet e hD
    rw [hcard] at hb
    norm_num at hb
  · obtain ⟨F, hF, hFM, hFcard, -⟩ := exists_cover_of_matrix_model M e hq
      (fun c hc => pow_eq_one_of_scalar_det (hdet _ hc)) hqn hD
    obtain ⟨hcomm, hexp⟩ := isElementaryAbelian_data hF
    have : Finite F := Finite.of_injective (fun x : F => (x : GL (Fin n) K)) Subtype.val_injective
    have hb := card_le_pow_pred_of_det_gl hq hqK F hcomm hexp (fun g hg => hdet g (hFM hg))
    rw [hFcard, hcard, Fintype.card_fin] at hb
    have h5 : q ^ 5 ≤ q ^ (n - 1) := hb
    have := (Nat.pow_le_pow_iff_right hq.one_lt).mp h5
    omega

theorem false_psl_five {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 5)
    (hmod : StatedClassicalModel T .PSL n 2 f) {q : ℕ} (hq : q.Prime) (hq37 : q = 3 ∨ q = 7)
    {D : Subgroup T} (hD : IsElementaryAbelian q D) (hcard : Nat.card D = q ^ 5) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card hK
  exact false_of_statedProj_det_five hn2 hn (StatedSL n K)
    (fun g hg => det_eq_one_of_mem_statedSL' hg) e hq hq37
    (natCast_ne_zero_of_charTwo (by rcases hq37 with rfl | rfl <;> rfl))
    (fun hodd => natCast_ne_zero_of_charTwo hodd) hD hcard

theorem false_psu_five {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 5)
    (hmod : StatedClassicalModel T .PSU n 2 f) {q : ℕ} (hq : q.Prime) (hq37 : q = 3 ∨ q = 7)
    {D : Subgroup T} (hD : IsElementaryAbelian q D) (hcard : Nat.card D = q ^ 5) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn3 : 3 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card (g := 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  exact false_of_statedProj_det_five (by omega) hn (StatedSU n (2 ^ f) K)
    (fun g hg => det_eq_one_of_mem_statedSU' hg) e hq hq37
    (natCast_ne_zero_of_charTwo (by rcases hq37 with rfl | rfl <;> rfl))
    (fun hodd => natCast_ne_zero_of_charTwo hodd) hD hcard

theorem false_of_form_five {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M) {q d : ℕ}
    (hq : q.Prime) (hqK : (q : K) ≠ 0)
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hqd : ¬ q ∣ d)
    (J : Matrix ι ι K) (hJ : J.det ≠ 0) (hAlt : ∀ v : ι → K, v ⬝ᵥ (J *ᵥ v) = 0)
    (hMJ : ∀ g ∈ M, ((g : GL ι K) : Matrix ι ι K)ᵀ * J * ((g : GL ι K) : Matrix ι ι K) = J)
    (hι : Fintype.card ι ≤ 8) {D : Subgroup T} (hD : IsElementaryAbelian q D)
    (hcard : Nat.card D = q ^ 5) : False := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨F, hF, hFM, hFcard, -⟩ := exists_cover_of_matrix_model M e hq hd hqd hD
  obtain ⟨hcomm, hexp⟩ := isElementaryAbelian_data hF
  have : Finite F := Finite.of_injective (fun x : F => (x : GL ι K)) Subtype.val_injective
  have hb := card_le_pow_half_of_form_gl hq hqK J hJ hAlt F hcomm hexp
    (fun g hg => hMJ g (hFM hg))
  rw [hFcard, hcard] at hb
  have h5 : q ^ 5 ≤ q ^ (Fintype.card ι / 2) := hb
  have := (Nat.pow_le_pow_iff_right hq.one_lt).mp h5
  omega

theorem false_psp_five {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .PSp n 2 f) {q : ℕ} (hq : q.Prime) (hq37 : q = 3 ∨ q = 7)
    {D : Subgroup T} (hD : IsElementaryAbelian q D) (hcard : Nat.card D = q ^ 5) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card hK
  refine false_of_form_five (StatedSp n K) e hq
    (natCast_ne_zero_of_charTwo (by rcases hq37 with rfl | rfl <;> rfl)) (d := 2) ?_
    (by rcases hq37 with rfl | rfl <;> decide) (symJ n K) (symJ_det_ne_zero n K)
    (symJ_alternating n K) (fun g hg => statedSp_le_isoGroup n K hg) (by simp; omega) hD hcard
  intro c hc
  have hJ := statedSp_le_isoGroup n K hc
  rw [mem_isoGroup] at hJ
  have h := congrFun (congrFun hJ (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
  simpa [symJ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.fromBlocks, Fintype.sum_sum_type] using h

theorem false_pomegaPlus_five {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaPlus n 2 f) {q : ℕ} (hq : q.Prime)
    (hq37 : q = 3 ∨ q = 7) {D : Subgroup T} (hD : IsElementaryAbelian q D)
    (hcard : Nat.card D = q ^ 5) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn4 : 4 ≤ n := hadm.2.2
  have : CharP K 2 := charP_two_of_card hK
  refine false_of_form_five (StatedOmega (StatedQuadPlus n K)) e hq
    (natCast_ne_zero_of_charTwo (by rcases hq37 with rfl | rfl <;> rfl)) (d := 2) ?_
    (by rcases hq37 with rfl | rfl <;> decide) (plusJ n K) (plusJ_det_ne_zero n)
    (alt_of_polar _ _ (quadPlus_polar n) (by simp [StatedQuadPlus]))
    (fun g hg => transpose_mul_eq_of_isoQ (quadPlus_polar n) (statedOmega_le_isoQ _ hg))
    (by simp; omega) hD hcard
  intro c hc
  exact sq_eq_one_of_scalar_mem_isoQ (quadPlus_smul n) (quadPlus_one n (by omega))
    (statedOmega_le_isoQ _ hc)

theorem false_pomegaMinus_five {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaMinus n 2 f) {q : ℕ} (hq : q.Prime)
    (hq37 : q = 3 ∨ q = 7) {D : Subgroup T} (hD : IsElementaryAbelian q D)
    (hcard : Nat.card D = q ^ 5) : False := by
  obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hmod
  have hn4 : 4 ≤ n := hadm.2.2
  have hchar : CharP K 2 := charP_two_of_card hK
  have hb : b ≠ 0 := by
    intro hb0
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
    apply hbc s
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [hb0, hs]
    linear_combination (s * s) * h2
  refine false_of_form_five (StatedOmega (StatedQuadMinus n K b c)) e hq
    (natCast_ne_zero_of_charTwo (by rcases hq37 with rfl | rfl <;> rfl)) (d := 2) ?_
    (by rcases hq37 with rfl | rfl <;> decide) (quadMinusJ n b) (quadMinusJ_det_ne_zero n hb)
    (alt_of_polar _ _ (quadMinus_polar n b c) (by simp [StatedQuadMinus]))
    (fun g hg => transpose_mul_eq_of_isoQ (quadMinus_polar n b c) (statedOmega_le_isoQ _ hg))
    (by simp; omega) hD hcard
  intro d hd
  exact sq_eq_one_of_scalar_mem_isoQ (quadMinus_smul n b c) (quadMinus_one n b c (by omega))
    (statedOmega_le_isoQ _ hd)

end CFSG.RankThree.PartOne.F106
