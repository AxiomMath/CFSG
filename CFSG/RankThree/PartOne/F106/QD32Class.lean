module

public import CFSG.RankThree.PartOne.F106.QD32Weyl
public import CFSG.RankThree.PartOne.BRANCH.RankClassical

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartOne.BRANCH

structure InducesQD32 {T : Type} [Group T] (E R : Subgroup T) : Prop where
  normalizes : R ≤ normalizer (E : Set T)
  hom : ∃ ψ : ↥R →* QD32, Function.Surjective ψ ∧
    ∀ r : ↥R, ψ r = 1 ↔ (r : T) ∈ centralizer (E : Set T)

theorem not_dvd_small {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5)
    (h33 : ¬ (q = 3 ∧ n = 3)) (hn2 : 2 ≤ n) (hn5 : n ≤ 5) : ¬ q ∣ n := by
  intro hdvd
  have hle : q ≤ 5 := (Nat.le_of_dvd (by omega) hdvd).trans hn5
  have h2 := hq.two_le
  interval_cases q <;> interval_cases n <;> first | omega | (exfalso; norm_num at hq)

theorem natCast_ne_zero_of_prime_ne_two {K : Type} [Field K] [CharP K 2] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) : (q : K) ≠ 0 :=
  natCast_ne_zero_of_charTwo (hq.eq_two_or_odd.resolve_left hq2)

theorem false_of_qd32_statedProj_det {n : ℕ} (hn : n < 16) {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL (Fin n) K))
    (hdet : ∀ g ∈ M, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) {T : Type} [Group T]
    (e : T ≃* StatedProj M) {q : ℕ} (hq : q.Prime) (hqK : (q : K) ≠ 0) (hqn : ¬ q ∣ n)
    {E R : Subgroup T} (hE : IsElementaryAbelian q E) (h : InducesQD32 E R) : False := by
  obtain ⟨ψ, hψs, hψc⟩ := h.hom
  exact false_of_qd32_matrix_model M e hq hqK (fun c hc => pow_eq_one_of_scalar_det (hdet _ hc))
    hqn (by simpa using hn) hE h.normalizes ψ hψs hψc

theorem scalar_pow_one_of_card_two {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) (M : Subgroup (GL ι K)) :
    ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ 1 = 1 := by
  intro c _
  have : Fintype K := Fintype.ofFinite K
  have h1 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have h2 := FiniteField.pow_card_sub_one_eq_one (c : K) c.ne_zero
  rw [h1] at h2
  exact Units.ext (by simpa using h2)

theorem false_psl_qd32 {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 5 ∨ ((n = 6 ∨ n = 7) ∧ f = 1))
    (hmod : StatedClassicalModel T .PSL n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5)
    (h33 : ¬ (q = 3 ∧ n = 3)) {E R : Subgroup T} (hE : IsElementaryAbelian q E)
    (h : InducesQD32 E R) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card hK
  have hqK : (q : K) ≠ 0 := natCast_ne_zero_of_prime_ne_two hq hq2
  rcases hn with hn5 | ⟨hn67, rfl⟩
  · exact false_of_qd32_statedProj_det (by omega) (StatedSL n K)
      (fun g hg => det_eq_one_of_mem_statedSL' hg) e hq hqK (not_dvd_small hq hq2 hq5 h33 hn2 hn5)
      hE h
  · obtain ⟨ψ, hψs, hψc⟩ := h.hom
    exact false_of_qd32_matrix_model (StatedSL n K) e hq hqK
      (scalar_pow_one_of_card_two (by simpa using hK) _) (d := 1) (by simp [hq.one_lt.ne'])
      (by simp; omega) hE h.normalizes ψ hψs hψc

theorem false_psu_qd32 {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 5 ∨ (n = 6 ∧ f = 1))
    (hmod : StatedClassicalModel T .PSU n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5)
    (h33 : ¬ (q = 3 ∧ (n = 3 ∨ n = 6))) {E R : Subgroup T} (hE : IsElementaryAbelian q E)
    (h : InducesQD32 E R) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn3 : 3 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card (g := 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  have hqK : (q : K) ≠ 0 := natCast_ne_zero_of_prime_ne_two hq hq2
  rcases hn with hn5 | ⟨rfl, rfl⟩
  · exact false_of_qd32_statedProj_det (by omega) (StatedSU n (2 ^ f) K)
      (fun g hg => det_eq_one_of_mem_statedSU' hg) e hq hqK
      (not_dvd_small hq hq2 hq5 (fun h3 => h33 ⟨h3.1, Or.inl h3.2⟩) (by omega) hn5) hE h
  · have hq6 : ¬ q ∣ 6 := by
      intro hdvd
      have hle : q ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      have h2 := hq.two_le
      interval_cases q <;> first | omega | (exfalso; norm_num at hq)
    exact false_of_qd32_statedProj_det (by omega) (StatedSU 6 (2 ^ 1) K)
      (fun g hg => det_eq_one_of_mem_statedSU' hg) e hq hqK hq6 hE h

theorem false_of_qd32_scalar_sq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) [CharP K 2]
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ 2 = 1)
    (hι : Fintype.card ι < 16) {E R : Subgroup T} (hE : IsElementaryAbelian q E)
    (h : InducesQD32 E R) : False := by
  obtain ⟨ψ, hψs, hψc⟩ := h.hom
  exact false_of_qd32_matrix_model M e hq (natCast_ne_zero_of_prime_ne_two hq hq2) hd
    (fun hdvd => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd)) hι hE h.normalizes ψ
    hψs hψc

theorem false_psp_qd32 {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .PSp n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {E R : Subgroup T} (hE : IsElementaryAbelian q E) (h : InducesQD32 E R) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card hK
  refine false_of_qd32_scalar_sq (StatedSp n K) e hq hq2 ?_ (by simp; omega) hE h
  intro c hc
  have hJ := statedSp_le_isoGroup n K hc
  rw [mem_isoGroup] at hJ
  have h := congrFun (congrFun hJ (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
  simpa [symJ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.fromBlocks, Fintype.sum_sum_type] using h

theorem false_pomegaPlus_qd32 {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaPlus n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {E R : Subgroup T} (hE : IsElementaryAbelian q E) (h : InducesQD32 E R) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn4 : 4 ≤ n := hadm.2.2
  have : CharP K 2 := charP_two_of_card hK
  refine false_of_qd32_scalar_sq (StatedOmega (StatedQuadPlus n K)) e hq hq2 ?_ (by simp; omega) hE
    h
  intro c hc
  exact sq_eq_one_of_scalar_mem_isoQ (quadPlus_smul n) (quadPlus_one n (by omega))
    (statedOmega_le_isoQ _ hc)

theorem false_pomegaMinus_qd32 {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaMinus n 2 f) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {E R : Subgroup T} (hE : IsElementaryAbelian q E) (h : InducesQD32 E R) : False := by
  obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hmod
  have hn4 : 4 ≤ n := hadm.2.2
  have hchar : CharP K 2 := charP_two_of_card hK
  refine false_of_qd32_scalar_sq (StatedOmega (StatedQuadMinus n K b c)) e hq hq2 ?_
    (by simp; omega) hE h
  intro d hd
  exact sq_eq_one_of_scalar_mem_isoQ (quadMinus_smul n b c) (quadMinus_one n b c (by omega))
    (statedOmega_le_isoQ _ hd)

end CFSG.RankThree.PartOne.F106
