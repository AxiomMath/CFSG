module

public import CFSG.Timmesfeld.Transvection.ModelSULine
public import CFSG.Timmesfeld.Transvection.ModelSUAut

import CFSG.Timmesfeld.Transvection.ModelSUFour
import CFSG.Timmesfeld.LieEmbed.UnitaryIsometry

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

private theorem map_add_smul_ends (x y : F) :
    (fun i : Fin (m + 2) => σ ((x • Pi.single (0 : Fin (m + 2)) 1 +
      y • Pi.single (Fin.last (m + 1)) 1 : Fin (m + 2) → F) i)) =
      (σ x • Pi.single (0 : Fin (m + 2)) 1 +
        σ y • Pi.single (Fin.last (m + 1)) 1 : Fin (m + 2) → F) := by
  funext i
  by_cases h0 : i = 0
  · subst h0
    simp [Pi.single_apply]
  · by_cases hL : i = Fin.last (m + 1)
    · subst hL
      simp [Pi.single_apply, h0]
    · simp [Pi.single_apply, h0, hL]

private theorem map_smul_single {j : Fin (m + 2)} (x : F) :
    (fun i => σ ((x • Pi.single j 1 : Fin (m + 2) → F) i)) = σ x • Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst h
    simp [Pi.single_apply]
  · simp [Pi.single_apply, h]

private theorem map_single_one (j : Fin (m + 2)) :
    (fun i => σ ((Pi.single j 1 : Fin (m + 2) → F) i)) = Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem map_suMat_eq_of_mem_lineSL {s : SU σ (m + 2)}
    (hs : s ∈ lineSL σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1)) :
    (suMat σ (m + 2) s).map σ = suMat σ (m + 2) s := by
  obtain ⟨hP, α, β, γ, δ, hα, hβ, hγ, hδ, hdet, hsa, hsd⟩ := hs
  ext i j
  rw [Matrix.map_apply]
  have hcol : (suMat σ (m + 2) s) i j = (suMat σ (m + 2) s *ᵥ Pi.single j 1) i := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcol]
  by_cases hj0 : j = 0
  · subst hj0
    rw [hsa]
    have h := map_add_smul_ends (σ := σ) (m := m) α β
    rw [hα, hβ] at h
    exact congrFun h i
  · by_cases hjL : j = Fin.last (m + 1)
    · subst hjL
      rw [hsd]
      have h := map_add_smul_ends (σ := σ) (m := m) γ δ
      rw [hγ, hδ] at h
      exact congrFun h i
    · have hmem : (Pi.single j 1 : Fin (m + 2) → F) ∈
          perpPair σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1) := by
        rw [mem_perpPair, uForm_single_left, uForm_single_left, Fin.rev_zero, Fin.rev_last]
        exact ⟨by simp [Pi.single_apply, hjL], by simp [Pi.single_apply, hj0]⟩
      rw [hP _ hmem]
      exact congrFun (map_single_one (σ := σ) (m := m) j) i

private theorem map_single_one_four (φ : F ≃+* F) (j : Fin 4) :
    (fun i => φ ((Pi.single j 1 : Fin 4 → F) i)) = Pi.single j 1 := by
  funext i
  fin_cases i <;> fin_cases j <;> simp

private theorem map_single_one_add_smul_single_two (φ : F ≃+* F) (s : F) :
    (fun i => φ ((Pi.single (1 : Fin 4) 1 + s • Pi.single (2 : Fin 4) 1 : Fin 4 → F) i)) =
      (Pi.single (1 : Fin 4) 1 + φ s • Pi.single (2 : Fin 4) 1 : Fin 4 → F) := by
  funext i
  fin_cases i <;> simp

private theorem uForm_single_one_add_smul_single_two [CharP F 2] {s : F} (hs : σ s = s) :
    uForm σ (Pi.single (1 : Fin 4) 1 + s • Pi.single (2 : Fin 4) 1 : Fin 4 → F)
      (Pi.single (1 : Fin 4) 1 + s • Pi.single (2 : Fin 4) 1) = 0 := by
  rw [uForm_eq, Fin.sum_univ_four]
  simp [Fin.rev_zero, Fin.rev_last, hs, CharTwo.add_self_eq_zero]

private theorem mem_perpPair_single_add_smul_single {s : F} :
    (Pi.single (1 : Fin 4) 1 + s • Pi.single (2 : Fin 4) 1 : Fin 4 → F) ∈
      perpPair σ (Pi.single (0 : Fin 4) 1) (Pi.single (3 : Fin 4) 1) := by
  rw [mem_perpPair, uForm_single_left, uForm_single_left]
  constructor <;> simp

private theorem mem_perpPair_single_four {j : Fin 4} (h0 : j ≠ 0) (h3 : j ≠ 3) :
    (Pi.single j 1 : Fin 4 → F) ∈
      perpPair σ (Pi.single (0 : Fin 4) 1) (Pi.single (3 : Fin 4) 1) := by
  rw [mem_perpPair, uForm_single_left, uForm_single_left]
  constructor <;> simp [Pi.single_apply, h0, h3]

theorem fixed_of_isotropic_eigen_four [CharP F 2]
    (M : Matrix (Fin 4) (Fin 4) F) (hMinj : ∀ v, M *ᵥ v = 0 → v = 0) (φ : F ≃+* F)
    (hM : ∀ u ∈ perpPair σ (Pi.single 0 1) (Pi.single 3 1), uForm σ u u = 0 →
      ∃ μ : F, M *ᵥ (fun i => φ (u i)) = μ • u) :
    (∀ c, σ c = c → φ c = c) ∧ ∃ l : F, l ≠ 0 ∧ M *ᵥ Pi.single 1 1 = l • Pi.single 1 1 ∧
      M *ᵥ Pi.single 2 1 = l • Pi.single 2 1 := by
  have hmem1 : (Pi.single (1 : Fin 4) 1 : Fin 4 → F) ∈
      perpPair σ (Pi.single 0 1) (Pi.single 3 1) :=
    mem_perpPair_single_four (by decide) (by decide)
  have hmem2 : (Pi.single (2 : Fin 4) 1 : Fin 4 → F) ∈
      perpPair σ (Pi.single 0 1) (Pi.single 3 1) :=
    mem_perpPair_single_four (by decide) (by decide)
  obtain ⟨μ1, hμ1⟩ := hM (Pi.single (1 : Fin 4) 1) hmem1
    (by simpa using uForm_single_one_add_smul_single_two (σ := σ) (s := 0) (map_zero σ))
  rw [map_single_one_four φ 1] at hμ1
  obtain ⟨μ2, hμ2⟩ := hM (Pi.single (2 : Fin 4) 1) hmem2 (uForm_single_self (by decide))
  rw [map_single_one_four φ 2] at hμ2
  have hcoef : ∀ s : F, σ s = s → ∃ μ : F, μ1 = μ ∧ φ s * μ2 = μ * s := by
    intro s hs
    obtain ⟨μ, hμ⟩ := hM (Pi.single (1 : Fin 4) 1 + s • Pi.single (2 : Fin 4) 1)
      (mem_perpPair_single_add_smul_single (σ := σ) (s := s))
      (uForm_single_one_add_smul_single_two hs)
    rw [map_single_one_add_smul_single_two φ s, mulVec_add, mulVec_smul, hμ1, hμ2] at hμ
    refine ⟨μ, ?_, ?_⟩
    · have h := congrFun hμ (1 : Fin 4)
      simpa using h
    · have h := congrFun hμ (2 : Fin 4)
      simpa using h
  have h21 : μ2 = μ1 := by
    obtain ⟨μ, h1, h2⟩ := hcoef 1 (map_one σ)
    rw [← h1, map_one φ, one_mul, mul_one] at h2
    exact h2
  have hμ1ne : μ1 ≠ 0 := by
    intro h
    have hz : M *ᵥ Pi.single (1 : Fin 4) 1 = 0 := by rw [hμ1, h, zero_smul]
    exact single_one_ne_zero 1 (hMinj _ hz)
  have hfix : ∀ c, σ c = c → φ c = c := by
    intro c hc
    obtain ⟨μ, h1, h2⟩ := hcoef c hc
    rw [← h1, h21, mul_comm μ1 c] at h2
    exact mul_right_cancel₀ hμ1ne h2
  exact ⟨hfix, μ1, hμ1ne, hμ1, by rw [← h21]; exact hμ2⟩

private theorem uForm_ends_four (x y x' y' : F) :
    uForm σ (x • Pi.single (0 : Fin 4) 1 + y • Pi.single (3 : Fin 4) 1 : Fin 4 → F)
      (x' • Pi.single (0 : Fin 4) 1 + y' • Pi.single (3 : Fin 4) 1) = σ x * y' + σ y * x' := by
  simp [uForm_add_left, uForm_smul_left, uForm_add_right, uForm_smul_right, uForm_single_left]
  ring

private theorem uForm_single_zero_three_four :
    uForm σ (Pi.single (0 : Fin 4) 1) (Pi.single (3 : Fin 4) 1) = 1 := by
  rw [uForm_single_left]
  simp

private theorem coord_eq_zero_of_isometry_four {B : Matrix (Fin 4) (Fin 4) F}
    (hiso : conjTr σ B * antidiag 4 * B = antidiag 4)
    (h1 : B *ᵥ Pi.single (1 : Fin 4) 1 = Pi.single 1 1)
    (h2 : B *ᵥ Pi.single (2 : Fin 4) 1 = Pi.single 2 1)
    {j : Fin 4} (hj : j = 0 ∨ j = 3) {k : Fin 4} (hk : k = 1 ∨ k = 2) :
    (B *ᵥ Pi.single j 1) k = 0 := by
  have key : ∀ m : Fin 4, (m = 1 ∨ m = 2) → (B *ᵥ Pi.single j 1) (Fin.rev m) = 0 := by
    intro m hm
    have h := uForm_mulVec_of_isometry hiso (Pi.single j 1) (Pi.single m 1)
    have hm' : B *ᵥ Pi.single m 1 = Pi.single m 1 := by
      rcases hm with rfl | rfl
      · exact h1
      · exact h2
    rw [hm', uForm_single_right, uForm_single_left] at h
    have hz : (Pi.single m 1 : Fin 4 → F) (Fin.rev j) = 0 := by
      rcases hj with rfl | rfl <;> rcases hm with rfl | rfl <;> simp
    rw [hz] at h
    exact (map_eq_zero σ).1 h
  rcases hk with rfl | rfl
  · simpa using key 2 (Or.inr rfl)
  · simpa using key 1 (Or.inl rfl)

private theorem eq_smul_ends_of_isometry_four {B : Matrix (Fin 4) (Fin 4) F}
    (hiso : conjTr σ B * antidiag 4 * B = antidiag 4)
    (h1 : B *ᵥ Pi.single (1 : Fin 4) 1 = Pi.single 1 1)
    (h2 : B *ᵥ Pi.single (2 : Fin 4) 1 = Pi.single 2 1)
    {j : Fin 4} (hj : j = 0 ∨ j = 3) :
    B *ᵥ Pi.single j 1 =
      (B *ᵥ Pi.single j 1) 0 • Pi.single (0 : Fin 4) 1 +
        (B *ᵥ Pi.single j 1) 3 • Pi.single (3 : Fin 4) 1 := by
  funext i
  by_cases hi0 : i = 0
  · subst hi0; simp
  · by_cases hi3 : i = 3
    · subst hi3; simp
    · have hk : i = 1 ∨ i = 2 := by
        fin_cases i
        · exact absurd rfl hi0
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd rfl hi3
      rw [coord_eq_zero_of_isometry_four hiso h1 h2 hj hk]
      simp [Pi.single_apply, hi0, hi3]

private theorem coeff_relations_of_isometry_four [CharP F 2]
    {B : Matrix (Fin 4) (Fin 4) F}
    (hiso : conjTr σ B * antidiag 4 * B = antidiag 4) (hBB : B * B.map σ = 1)
    {p r p' r' : F}
    (h0 : B *ᵥ Pi.single (0 : Fin 4) 1 = p • Pi.single 0 1 + r • Pi.single (3 : Fin 4) 1)
    (h3 : B *ᵥ Pi.single (3 : Fin 4) 1 = p' • Pi.single 0 1 + r' • Pi.single 3 1) :
    r' = p ∧ σ p * p + σ r * p' = 1 ∧ σ p * r + σ r * r' = 0 := by
  have h00 : σ p * r + σ r * p = 0 := by
    have h := uForm_mulVec_of_isometry hiso (Pi.single (0 : Fin 4) 1) (Pi.single (0 : Fin 4) 1)
    rw [h0, uForm_single_self (by decide), uForm_ends_four] at h
    exact h
  have h03 : σ p * r' + σ r * p' = 1 := by
    have h := uForm_mulVec_of_isometry hiso (Pi.single (0 : Fin 4) 1) (Pi.single (3 : Fin 4) 1)
    rw [h0, h3, uForm_ends_four, uForm_single_zero_three_four] at h
    exact h
  have hBσ0 : (B.map σ) *ᵥ Pi.single (0 : Fin 4) 1 =
      σ p • Pi.single (0 : Fin 4) 1 + σ r • Pi.single (3 : Fin 4) 1 := by
    have hmap : (B.map σ) *ᵥ Pi.single (0 : Fin 4) 1 =
        fun i => σ ((B *ᵥ Pi.single (0 : Fin 4) 1) i) := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mulVec_single_one,
        Matrix.col_apply]
      rfl
    rw [hmap, h0]
    exact map_add_smul_ends (σ := σ) (m := 2) p r
  have hBB0 : B *ᵥ ((B.map σ) *ᵥ Pi.single (0 : Fin 4) 1) = Pi.single (0 : Fin 4) 1 := by
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M *ᵥ Pi.single (0 : Fin 4) 1) hBB
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h
    exact h
  have hrel : σ p * p + σ r * p' = 1 ∧ σ p * r + σ r * r' = 0 := by
    have h := hBB0
    rw [hBσ0, mulVec_add, mulVec_smul, mulVec_smul, h0, h3] at h
    constructor
    · have h' := congrFun h (0 : Fin 4)
      simpa using h'
    · have h' := congrFun h (3 : Fin 4)
      simpa using h'
  have hsum : σ p * (r' + p) = 0 := by
    have h : σ p * r' + σ r * p' = σ p * p + σ r * p' := by rw [h03, hrel.1]
    have h2 : σ p * r' = σ p * p := add_right_cancel h
    rw [mul_add, h2, CharTwo.add_self_eq_zero]
  have hsum2 : σ r * (r' + p) = 0 := by
    have h : σ p * r + σ r * r' = σ p * r + σ r * p := by rw [hrel.2, h00]
    have h2 : σ r * r' = σ r * p := add_left_cancel h
    rw [mul_add, h2, CharTwo.add_self_eq_zero]
  have hrp : r' + p = 0 := by
    rcases mul_eq_zero.mp hsum with h' | h'
    · rcases mul_eq_zero.mp hsum2 with h'' | h''
      · exfalso
        have h1 : σ p = 0 := h'
        have h2 : σ r = 0 := h''
        rw [h1, h2, zero_mul, zero_mul, add_zero] at h03
        exact zero_ne_one h03
      · exact h''
    · exact h'
  have : r' = p := by
    calc r' = r' + 0 := (add_zero r').symm
      _ = r' + (p + p) := by rw [CharTwo.add_self_eq_zero]
      _ = (r' + p) + p := by abel
      _ = p := by rw [hrp, zero_add]
  exact ⟨this, hrel.1, hrel.2⟩

private theorem commute_coeff_four [CharP F 2]
    {B : Matrix (Fin 4) (Fin 4) F} {s : SU σ 4} {α β γ δ p r p' r' : F}
    (hB0 : B *ᵥ Pi.single (0 : Fin 4) 1 = p • Pi.single 0 1 + r • Pi.single 3 1)
    (hB3 : B *ᵥ Pi.single (3 : Fin 4) 1 = p' • Pi.single 0 1 + r' • Pi.single 3 1)
    (hsa : suMat σ 4 s *ᵥ Pi.single (0 : Fin 4) 1 = α • Pi.single 0 1 + β • Pi.single 3 1)
    (hsd : suMat σ 4 s *ᵥ Pi.single (3 : Fin 4) 1 = γ • Pi.single 0 1 + δ • Pi.single 3 1)
    (hBs : B * suMat σ 4 s = suMat σ 4 s * B) (hrp : r' = p) :
    r * (α + δ) = 0 ∧ p' * (α + δ) = 0 := by
  have h0 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M *ᵥ Pi.single (0 : Fin 4) 1) hBs
  have h3 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M *ᵥ Pi.single (3 : Fin 4) 1) hBs
  rw [← Matrix.mulVec_mulVec, hsa, ← Matrix.mulVec_mulVec, hB0, mulVec_add, mulVec_smul,
    mulVec_smul, hB0, hB3, mulVec_add, mulVec_smul, mulVec_smul, hsa, hsd] at h0
  rw [← Matrix.mulVec_mulVec, hsd, ← Matrix.mulVec_mulVec, hB3, mulVec_add, mulVec_smul,
    mulVec_smul, hB0, hB3, mulVec_add, mulVec_smul, mulVec_smul, hsa, hsd] at h3
  constructor
  · have h := congrFun h0 (3 : Fin 4)
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 0), smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add] at h
    rw [hrp, mul_comm p β] at h
    rw [add_comm (β * p) (r * δ)] at h
    have h2 : α * r = r * δ := add_right_cancel h
    calc r * (α + δ) = r * α + r * δ := mul_add r α δ
      _ = α * r + r * δ := by rw [mul_comm r α]
      _ = r * δ + r * δ := by rw [← h2]
      _ = 0 := CharTwo.add_self_eq_zero _
  · have h := congrFun h3 (0 : Fin 4)
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 3), smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add] at h
    rw [hrp, mul_comm p γ] at h
    rw [add_comm (p' * α) (γ * p)] at h
    have h2 : δ * p' = p' * α := add_left_cancel h
    calc p' * (α + δ) = p' * α + p' * δ := mul_add p' α δ
      _ = δ * p' + p' * δ := by rw [← h2]
      _ = p' * δ + p' * δ := by rw [mul_comm δ p']
      _ = 0 := CharTwo.add_self_eq_zero _

theorem exists_smul_ends_four [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {B : Matrix (Fin 4) (Fin 4) F}
    (hiso : conjTr σ B * antidiag 4 * B = antidiag 4) (hBB : B * B.map σ = 1)
    (h1 : B *ᵥ Pi.single 1 1 = Pi.single 1 1) (h2 : B *ᵥ Pi.single 2 1 = Pi.single 2 1)
    {s : SU σ 4} (hs : s ∈ lineSL σ (Pi.single 0 1) (Pi.single 3 1)) (hs2 : s * s ≠ 1)
    (hBs : B * suMat σ 4 s = suMat σ 4 s * B) :
    ∃ x : F, σ x * x = 1 ∧ B *ᵥ Pi.single 0 1 = x • Pi.single 0 1 ∧
      B *ᵥ Pi.single 3 1 = x • Pi.single 3 1 := by
  obtain ⟨hP, α, β, γ, δ, hα, hβ, hγ, hδ, hdet, hsa, hsd⟩ := hs
  obtain ⟨p, r, p', r', hB0, hB3⟩ :
      ∃ p r p' r' : F,
        B *ᵥ Pi.single (0 : Fin 4) 1 = p • Pi.single 0 1 + r • Pi.single 3 1 ∧
          B *ᵥ Pi.single (3 : Fin 4) 1 = p' • Pi.single 0 1 + r' • Pi.single 3 1 :=
    ⟨(B *ᵥ Pi.single 0 1) 0, (B *ᵥ Pi.single 0 1) 3, (B *ᵥ Pi.single 3 1) 0,
      (B *ᵥ Pi.single 3 1) 3, eq_smul_ends_of_isometry_four hiso h1 h2 (Or.inl rfl),
      eq_smul_ends_of_isometry_four hiso h1 h2 (Or.inr rfl)⟩
  obtain ⟨hrp, hnorm, -⟩ := coeff_relations_of_isometry_four hiso hBB hB0 hB3
  have hαδ : α + δ ≠ 0 := by
    intro h0
    exact hs2 (mul_self_eq_one_of_add_eq_zero (σ := σ) (m := 4) hσ
      (uForm_single_self (by decide)) (uForm_single_self (by decide))
      uForm_single_zero_three_four hP hdet hsa hsd h0)
  obtain ⟨hr0, hp'0⟩ := commute_coeff_four hB0 hB3 hsa hsd hBs hrp
  have hr : r = 0 := (mul_eq_zero.mp hr0).resolve_right hαδ
  have hp' : p' = 0 := (mul_eq_zero.mp hp'0).resolve_right hαδ
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [hr, hp'] at hnorm
    simpa using hnorm
  · rw [hB0, hr, zero_smul, add_zero]
  · rw [hB3, hp', hrp, zero_smul, zero_add]

private theorem scalar_mul_map_of_semilinear_four [CharP F 2] {K : Type*} [Group K]
    {Φ : SU σ 4 →* K} {y : K} {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU σ 4 →* SU σ 4} (hL : IsSemilinearLift Φ y A φ α)
    (hφ : ∀ c, φ c = σ c) (hαα : ∀ g, α (α g) = g) (hσ : ∀ c, σ (σ c) = c) :
    ∃ cc : F, (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F).map σ =
      cc • 1 := by
  have hφφ : ∀ c, (φ.trans φ) c = c := by
    intro c
    change φ (φ c) = c
    rw [hφ (φ c), hφ c, hσ c]
  have hmapid : ∀ g : SU σ 4, (suMat σ 4 g).map (φ.trans φ) = suMat σ 4 g := by
    intro g
    ext a b
    rw [Matrix.map_apply]
    exact hφφ _
  have hM : ∀ g : SU σ 4,
      ((A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F).map σ) *
          suMat σ 4 g =
        suMat σ 4 g *
          ((A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F).map σ) := by
    intro g
    have h := (hL.comp hL).mat g
    rw [MonoidHom.comp_apply, hαα g, hmapid g, Units.val_mul, coe_glAut] at h
    rw [show (A : Matrix (Fin 4) (Fin 4) F).map φ =
        (A : Matrix (Fin 4) (Fin 4) F).map σ from by
      ext a b
      exact hφ _] at h
    exact h.symm
  exact exists_smul_one_of_commute_SU_four hσ hM

private theorem exists_normalized_isometry_four [CharP F 2] {K : Type*} [Group K]
    {Φ : SU σ 4 →* K} {y : K} {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU σ 4 →* SU σ 4} (hL : IsSemilinearLift Φ y A φ α)
    (hφ : ∀ c, φ c = σ c) (hαα : ∀ g, α (α g) = g) (hσ : ∀ c, σ (σ c) = c) {l : F}
    (h1 : (A : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single 1 1 = l • Pi.single 1 1)
    (h2 : (A : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single 2 1 = l • Pi.single 2 1) :
    ∃ B : Matrix (Fin 4) (Fin 4) F, conjTr σ B * antidiag 4 * B = antidiag 4 ∧
      B * B.map σ = 1 ∧ B *ᵥ Pi.single 1 1 = Pi.single 1 1 ∧
        B *ᵥ Pi.single 2 1 = Pi.single 2 1 ∧
          (A : Matrix (Fin 4) (Fin 4) F) = l • B ∧ l ≠ 0 := by
  obtain ⟨cc, hcc⟩ := scalar_mul_map_of_semilinear_four hL hφ hαα hσ
  have hpair : uForm σ (Pi.single (1 : Fin 4) 1) (Pi.single (2 : Fin 4) 1) = 1 := by
    rw [uForm_single_left]
    simp
  have hll : σ l * l = 1 := by
    have h := uForm_mulVec_of_isometry (σ := σ) (n := 4) hL.isometry
      (Pi.single (1 : Fin 4) 1) (Pi.single (2 : Fin 4) 1)
    rw [h1, h2, hpair, uForm_smul_left, uForm_smul_right, hpair, mul_one] at h
    exact h
  have hl0 : l ≠ 0 := by
    intro hl
    have h : (0 : F) = 1 := by simpa [hl] using hll
    exact zero_ne_one h
  have hAσ1 : (A : Matrix (Fin 4) (Fin 4) F).map σ *ᵥ Pi.single (1 : Fin 4) 1 =
      σ l • Pi.single (1 : Fin 4) 1 := by
    have hmap : (A : Matrix (Fin 4) (Fin 4) F).map σ *ᵥ Pi.single (1 : Fin 4) 1 =
        fun i => σ ((A *ᵥ Pi.single (1 : Fin 4) 1) i) := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mulVec_single_one, Matrix.col_apply]
      rfl
    rw [hmap, h1]
    exact map_smul_single (σ := σ) (m := 2) (j := 1) l
  have hccval : cc = σ l * l := by
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M *ᵥ Pi.single (1 : Fin 4) 1) hcc
    rw [← Matrix.mulVec_mulVec, hAσ1, Matrix.mulVec_smul, h1, smul_smul, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h
    have h' : σ l * l = cc := by
      have h'' := congrFun h (1 : Fin 4)
      simpa using h''
    exact h'.symm
  have hσlinv : σ l⁻¹ * l⁻¹ = 1 := by
    rw [map_inv₀, ← _root_.mul_inv_rev, mul_comm l (σ l), hll, inv_one]
  have hconjTr_smul : conjTr σ (l⁻¹ • (A : Matrix (Fin 4) (Fin 4) F)) =
      σ l⁻¹ • conjTr σ (A : Matrix (Fin 4) (Fin 4) F) := by
    ext a b
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      map_mul]
  have hmapBm : (l⁻¹ • (A : Matrix (Fin 4) (Fin 4) F)).map σ =
      σ l⁻¹ • (A : Matrix (Fin 4) (Fin 4) F).map σ := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  refine ⟨l⁻¹ • (A : Matrix (Fin 4) (Fin 4) F), ?_, ?_, ?_, ?_, ?_, hl0⟩
  · rw [hconjTr_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hL.isometry,
      smul_smul, hσlinv, one_smul]
  · rw [hmapBm, Matrix.smul_mul, Matrix.mul_smul, hcc]
    simpa only [smul_smul, smul_eq_mul, mul_comm l⁻¹ (σ l⁻¹), hσlinv, hccval, hll, one_mul,
      mul_one, one_smul]
  · rw [Matrix.smul_mulVec, h1, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  · rw [Matrix.smul_mulVec, h2, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  · rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]

private theorem commute_suMat_of_semilinear_four [CharP F 2] {K : Type*} [Group K]
    {Φ : SU σ 4 →* K} {y : K} {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU σ 4 →* SU σ 4} (hL : IsSemilinearLift Φ y A φ α)
    (hΦ : Function.Injective Φ) (hφ : ∀ c, φ c = σ c) {l : F} (hl0 : l ≠ 0)
    {B : Matrix (Fin 4) (Fin 4) F} (hAB : (A : Matrix (Fin 4) (Fin 4) F) = l • B)
    {s : SU σ 4} (hs : s ∈ lineSL σ (Pi.single 0 1) (Pi.single 3 1))
    (hys : y * Φ s = Φ s * y) :
    B * suMat σ 4 s = suMat σ 4 s * B := by
  have hαs : α s = s := by
    refine hΦ ?_
    rw [hL.conj s, hys, mul_assoc, mul_inv_cancel, mul_one]
  have hsp : (suMat σ 4 s).map φ = suMat σ 4 s := by
    rw [show (suMat σ 4 s).map φ = (suMat σ 4 s).map σ from by
      ext a b
      exact hφ _
      , map_suMat_eq_of_mem_lineSL (σ := σ) hs]
  have hAs : suMat σ 4 s * (A : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) * suMat σ 4 s := by
    have h := hL.mat s
    rw [hαs, hsp] at h
    exact h
  have h := hAs
  rw [hAB, Matrix.mul_smul, Matrix.smul_mul] at h
  have h' := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => l⁻¹ • M) h
  simpa only [smul_smul, inv_mul_cancel₀ hl0, one_smul] using h'.symm

private theorem alpha_eq_of_commute_four [CharP F 2] {K : Type*} [Group K]
    {Φ : SU σ 4 →* K} {y : K} {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU σ 4 →* SU σ 4} (hL : IsSemilinearLift Φ y A φ α) (hφ : ∀ c, φ c = σ c)
    {l : F} (hl0 : l ≠ 0) {B : Matrix (Fin 4) (Fin 4) F}
    (hAB : (A : Matrix (Fin 4) (Fin 4) F) = l • B)
    (hisoB : conjTr σ B * antidiag 4 * B = antidiag 4) (hBB : B * B.map σ = 1)
    {i : Fin 4} {x : F} (hxnorm : σ x * x = 1)
    (hbe : B *ᵥ Pi.single i 1 = x • Pi.single i 1)
    {t : SU σ 4} {c : F} (hc : c + σ c = 0) (ht : suMat σ 4 t = uTrans σ (Pi.single i 1) c) :
    α t = t := by
  have hσc : σ c = c := by
    have h : σ c + c = 0 := by rw [add_comm]; exact hc
    calc σ c = σ c + 0 := (add_zero _).symm
      _ = σ c + (c + c) := by rw [CharTwo.add_self_eq_zero]
      _ = (σ c + c) + c := by abel
      _ = c := by rw [h, zero_add]
  have hφc : φ c = c := by rw [hφ c, hσc]
  have hmap : (suMat σ 4 t).map φ = uTrans σ (Pi.single i 1) c := by
    rw [ht, map_uTrans φ hL.comm, map_single_one_four φ i, hφc]
  have h := hL.mat t
  rw [hmap, hAB, Matrix.mul_smul, Matrix.smul_mul] at h
  have h' := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => l⁻¹ • M) h
  simp only [smul_smul, inv_mul_cancel₀ hl0, one_smul] at h'
  have hR : B * uTrans σ (Pi.single i 1) c = uTrans σ (Pi.single i 1) c * B := by
    rw [mul_uTrans_of_isometry hisoB, hbe, uTrans_smul,
      show x * σ x = 1 from by rw [mul_comm, hxnorm], one_mul]
  rw [hR] at h'
  have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M * B.map σ) h'
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one, Matrix.mul_one] at hh
  exact suMat_injective σ (by rw [hh, ht])

theorem IsSemilinearLift.commute_of_sigma_four [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {K : Type*} [Group K]
    {Φ : SU (unitaryInvolution F 2 f) 4 →* K} (hΦ : Function.Injective Φ) {y : K}
    {A : GL (Fin 4) F} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) 4 →* SU (unitaryInvolution F 2 f) 4}
    (hL : IsSemilinearLift Φ y A φ α) (hφ : ∀ c, φ c = unitaryInvolution F 2 f c)
    (hαα : ∀ g, α (α g) = g) {l : F}
    (h1 : (A : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single 1 1 = l • Pi.single 1 1)
    (h2 : (A : Matrix (Fin 4) (Fin 4) F) *ᵥ Pi.single 2 1 = l • Pi.single 2 1)
    {s : SU (unitaryInvolution F 2 f) 4}
    (hs : s ∈ lineSL (unitaryInvolution F 2 f) (Pi.single 0 1) (Pi.single 3 1))
    (hs2 : s * s ≠ 1) (hys : y * Φ s = Φ s * y) {i : Fin 4} (hi : i = 0 ∨ i = 3)
    {t : SU (unitaryInvolution F 2 f) 4} {c : F} (hc : c + unitaryInvolution F 2 f c = 0)
    (ht : suMat (unitaryInvolution F 2 f) 4 t =
      uTrans (unitaryInvolution F 2 f) (Pi.single i 1) c) :
    y * Φ t = Φ t * y := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨B, hisoB, hBB, hB1, hB2, hAB, hl0⟩ :=
    exists_normalized_isometry_four hL hφ hαα hσ h1 h2
  have hBs := commute_suMat_of_semilinear_four hL hΦ hφ hl0 hAB hs hys
  obtain ⟨x, hxnorm, hx0, hx3⟩ := exists_smul_ends_four hσ hisoB hBB hB1 hB2 hs hs2 hBs
  have hαt : α t = t := by
    rcases hi with rfl | rfl
    · exact alpha_eq_of_commute_four hL hφ hl0 hAB hisoB hBB hxnorm hx0 hc ht
    · exact alpha_eq_of_commute_four hL hφ hl0 hAB hisoB hBB hxnorm hx3 hc ht
  have hconj := hL.conj t
  rw [hαt] at hconj
  have key : (y * Φ t * y⁻¹) * y = y * Φ t := by group
  rw [hconj.symm] at key
  exact key.symm

end ModelRank

end CFSG.Timmesfeld.Transvection
