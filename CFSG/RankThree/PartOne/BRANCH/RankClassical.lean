module

public import CFSG.RankThree.PartOne.BRANCH.RankProj
public import CFSG.RankThree.PartOne.N143X.EvenOrth

public section

namespace CFSG.RankThree.PartOne.BRANCH

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143X
  CFSG.RankThree.PartOne.LIT

theorem isElementaryAbelian_data {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {q : ℕ} {F : Subgroup (GL ι K)} (hF : IsElementaryAbelian q F) :
    (∀ g ∈ F, ∀ h ∈ F, g * h = h * g) ∧ ∀ g ∈ F, g ^ q = 1 :=
  ⟨fun g hg h hh => congrArg Subtype.val (hF.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩),
    fun g hg => elemPow_eq_one_of_isElementaryAbelian (p := q) g hg⟩

theorem false_of_statedProj_det {n : ℕ} (hn2 : 2 ≤ n) (hn5 : n ≤ 5) {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL (Fin n) K))
    (hdet : ∀ g ∈ M, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) {T : Type} [Group T]
    (e : T ≃* StatedProj M) {q : ℕ} (hq : q.Prime) (hq35 : q = 3 ∨ q = 5) (hqK : (q : K) ≠ 0)
    (hnK : n % 2 = 1 → (n : K) ≠ 0) {D : Subgroup T} (hD : IsElementaryAbelian q D)
    (hcard : Nat.card D = q ^ 7) : False := by
  have : Fact q.Prime := ⟨hq⟩
  rcases Nat.even_or_odd n with hev | hodd
  ·
    have hn24 : n = 2 ∨ n = 4 := by
      obtain ⟨k, hk⟩ := hev
      omega
    have hqn : ¬ q ∣ n := by
      rcases hq35 with rfl | rfl <;> rcases hn24 with rfl | rfl <;> decide
    obtain ⟨F, hF, hFM, hFcard, -⟩ := exists_cover_of_matrix_model M e hq
      (fun c hc => pow_eq_one_of_scalar_det (hdet _ hc)) hqn hD
    obtain ⟨hcomm, hexp⟩ := isElementaryAbelian_data hF
    have : Finite F := Finite.of_injective (fun x : F => (x : GL (Fin n) K)) Subtype.val_injective
    have hb := card_le_pow_pred_of_det_gl hq hqK F hcomm hexp (fun g hg => hdet g (hFM hg))
    rw [hFcard, hcard, Fintype.card_fin] at hb
    have h7 : q ^ 7 ≤ q ^ (n - 1) := hb
    have := Nat.pow_le_pow_iff_right hq.one_lt |>.mp h7
    omega
  · have hn35 : n = 3 ∨ n = 5 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hb := card_le_of_statedProj hq hqK (hnK (by rcases hn35 with rfl | rfl <;> rfl)) M hdet e
      hD
    rw [hcard] at hb
    rcases hq35 with rfl | rfl <;> rcases hn35 with rfl | rfl <;> norm_num at hb

theorem alt_of_polar {ι : Type} [Fintype ι] {K : Type} [Field K] [CharP K 2]
    (Q : (ι → K) → K) (J : Matrix ι ι K)
    (hpolar : ∀ v w, Q (v + w) = Q v + Q w + v ⬝ᵥ (J *ᵥ w)) (hQ0 : Q 0 = 0) :
    ∀ v, v ⬝ᵥ (J *ᵥ v) = 0 := by
  intro v
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hvv : v + v = 0 := by
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    linear_combination (v i) * h2
  have h := hpolar v v
  rw [hvv, hQ0] at h
  linear_combination (-1 : K) * h - (Q v) * h2

theorem symJ_alternating (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n → K) :
    v ⬝ᵥ (symJ n K *ᵥ v) = 0 := by
  simp only [symJ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  simp [Matrix.one_apply, mul_comm]

theorem natCast_ne_zero_of_charTwo {K : Type} [Field K] [CharP K 2] {m : ℕ} (hm : m % 2 = 1) :
    (m : K) ≠ 0 := fun h => by
  have := (CharP.cast_eq_zero_iff K 2 m).mp h
  omega

theorem false_psl {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 5)
    (hmod : StatedClassicalModel T .PSL n 2 f) {q : ℕ} (hq : q.Prime) (hq35 : q = 3 ∨ q = 5)
    {D : Subgroup T} (hD : IsElementaryAbelian q D) (hcard : Nat.card D = q ^ 7) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card hK
  exact false_of_statedProj_det hn2 hn (StatedSL n K)
    (fun g hg => det_eq_one_of_mem_statedSL' hg) e hq hq35
    (natCast_ne_zero_of_charTwo (by rcases hq35 with rfl | rfl <;> rfl))
    (fun hodd => natCast_ne_zero_of_charTwo hodd) hD hcard

theorem false_psu {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 5)
    (hmod : StatedClassicalModel T .PSU n 2 f) {q : ℕ} (hq : q.Prime) (hq35 : q = 3 ∨ q = 5)
    {D : Subgroup T} (hD : IsElementaryAbelian q D) (hcard : Nat.card D = q ^ 7) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn3 : 3 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card (g := 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  exact false_of_statedProj_det (by omega) hn (StatedSU n (2 ^ f) K)
    (fun g hg => det_eq_one_of_mem_statedSU' hg) e hq hq35
    (natCast_ne_zero_of_charTwo (by rcases hq35 with rfl | rfl <;> rfl))
    (fun hodd => natCast_ne_zero_of_charTwo hodd) hD hcard

theorem false_of_form {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M) {q d : ℕ}
    (hq : q.Prime) (hqK : (q : K) ≠ 0)
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hqd : ¬ q ∣ d)
    (J : Matrix ι ι K) (hJ : J.det ≠ 0) (hAlt : ∀ v : ι → K, v ⬝ᵥ (J *ᵥ v) = 0)
    (hMJ : ∀ g ∈ M, ((g : GL ι K) : Matrix ι ι K)ᵀ * J * ((g : GL ι K) : Matrix ι ι K) = J)
    (hι : Fintype.card ι ≤ 8) {D : Subgroup T} (hD : IsElementaryAbelian q D)
    (hcard : Nat.card D = q ^ 7) : False := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨F, hF, hFM, hFcard, -⟩ := exists_cover_of_matrix_model M e hq hd hqd hD
  obtain ⟨hcomm, hexp⟩ := isElementaryAbelian_data hF
  have : Finite F := Finite.of_injective (fun x : F => (x : GL ι K)) Subtype.val_injective
  have hb := card_le_pow_half_of_form_gl hq hqK J hJ hAlt F hcomm hexp
    (fun g hg => hMJ g (hFM hg))
  rw [hFcard, hcard] at hb
  have h7 : q ^ 7 ≤ q ^ (Fintype.card ι / 2) := hb
  have := (Nat.pow_le_pow_iff_right hq.one_lt).mp h7
  omega

theorem false_psp {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .PSp n 2 f) {q : ℕ} (hq : q.Prime) (hq35 : q = 3 ∨ q = 5)
    {D : Subgroup T} (hD : IsElementaryAbelian q D) (hcard : Nat.card D = q ^ 7) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : CharP K 2 := charP_two_of_card hK
  refine false_of_form (StatedSp n K) e hq
    (natCast_ne_zero_of_charTwo (by rcases hq35 with rfl | rfl <;> rfl)) (d := 2) ?_
    (by rcases hq35 with rfl | rfl <;> decide) (symJ n K) (symJ_det_ne_zero n K)
    (symJ_alternating n K) (fun g hg => statedSp_le_isoGroup n K hg) (by simp; omega) hD hcard
  intro c hc
  have hJ := statedSp_le_isoGroup n K hc
  rw [mem_isoGroup] at hJ
  have h := congrFun (congrFun hJ (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, sq]
  simpa [symJ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.fromBlocks, Fintype.sum_sum_type] using h

theorem false_pomegaPlus {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaPlus n 2 f) {q : ℕ} (hq : q.Prime)
    (hq35 : q = 3 ∨ q = 5) {D : Subgroup T} (hD : IsElementaryAbelian q D)
    (hcard : Nat.card D = q ^ 7) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hn4 : 4 ≤ n := hadm.2.2
  have : CharP K 2 := charP_two_of_card hK
  refine false_of_form (StatedOmega (StatedQuadPlus n K)) e hq
    (natCast_ne_zero_of_charTwo (by rcases hq35 with rfl | rfl <;> rfl)) (d := 2) ?_
    (by rcases hq35 with rfl | rfl <;> decide) (plusJ n K) (plusJ_det_ne_zero n)
    (alt_of_polar _ _ (quadPlus_polar n) (by simp [StatedQuadPlus]))
    (fun g hg => transpose_mul_eq_of_isoQ (quadPlus_polar n) (statedOmega_le_isoQ _ hg))
    (by simp; omega) hD hcard
  intro c hc
  exact sq_eq_one_of_scalar_mem_isoQ (quadPlus_smul n) (quadPlus_one n (by omega))
    (statedOmega_le_isoQ _ hc)

theorem false_pomegaMinus {T : Type} [Group T] {n f : ℕ} (hn : n ≤ 4)
    (hmod : StatedClassicalModel T .POmegaMinus n 2 f) {q : ℕ} (hq : q.Prime)
    (hq35 : q = 3 ∨ q = 5) {D : Subgroup T} (hD : IsElementaryAbelian q D)
    (hcard : Nat.card D = q ^ 7) : False := by
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
  refine false_of_form (StatedOmega (StatedQuadMinus n K b c)) e hq
    (natCast_ne_zero_of_charTwo (by rcases hq35 with rfl | rfl <;> rfl)) (d := 2) ?_
    (by rcases hq35 with rfl | rfl <;> decide) (quadMinusJ n b) (quadMinusJ_det_ne_zero n hb)
    (alt_of_polar _ _ (quadMinus_polar n b c) (by simp [StatedQuadMinus]))
    (fun g hg => transpose_mul_eq_of_isoQ (quadMinus_polar n b c) (statedOmega_le_isoQ _ hg))
    (by simp; omega) hD hcard
  intro d hd
  exact sq_eq_one_of_scalar_mem_isoQ (quadMinus_smul n b c) (quadMinus_one n b c (by omega))
    (statedOmega_le_isoQ _ hd)

end CFSG.RankThree.PartOne.BRANCH
