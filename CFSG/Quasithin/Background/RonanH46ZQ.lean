module

public import CFSG.Quasithin.Background.RonanH46ZBase

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem QZs_entries {g : SL(3, K)} (hg : g ∈ QZs K) :
    (g : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
  rw [QZs_eq_Q1] at hg
  obtain ⟨x00, x11, x22, x10, x20, x21⟩ := uni3_entries hg.1
  have x12 : (g : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := hg.2
  exact ⟨x00, x11, x22, x10, x20, x21, x12⟩

theorem QZs_le_perfZ : QZs K ≤ perfZ K := by
  intro g hg
  obtain ⟨h00, -, -, h10, h20, -, -⟩ := QZs_entries hg
  exact ⟨h10, h20, h00⟩

theorem exists_QZs (s₀ s₁ : K) :
    ∃ g ∈ QZs K, (g : Matrix (Fin 3) (Fin 3) K) 0 1 = s₀ ∧
      (g : Matrix (Fin 3) (Fin 3) K) 0 2 = s₁ := by
  refine ⟨SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) s₀ *
    SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) s₁,
    mul_mem (Subgroup.subset_closure ⟨s₀, Or.inl rfl⟩)
      (Subgroup.subset_closure ⟨s₁, Or.inr rfl⟩), ?_, ?_⟩ <;>
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.single_apply]

private theorem QZs_blk_eq_one {g : SL(3, K)} (hg : g ∈ QZs K) :
    blkMatZ (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
  obtain ⟨-, h11, h22, -, -, h21, h12⟩ := QZs_entries hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMatZ, h11, h22, h21, h12]

theorem QZ_act_block (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ QZs K)
    (X : HMod n K) : hermBlkZ (rho hK g X) = hermBlkZ X := by
  rw [rhoZ_block hK (QZs_le_perfZ hg), QZs_blk_eq_one hg,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one]

theorem QZ_act_row (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ QZs K)
    (X : HMod n K) (j : Fin 2) :
    mat (rho hK g X) 0 j.succ = mat X 0 j.succ +
      ((g : Matrix (Fin 3) (Fin 3) K) 0 1 * mat X 1 j.succ +
        (g : Matrix (Fin 3) (Fin 3) K) 0 2 * mat X 2 j.succ) := by
  rw [rhoZ_row hK (QZs_le_perfZ hg), QZs_blk_eq_one hg,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.vecMul_one]
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hermBlkZ]

theorem QZ_act_corner (hK : Nat.card K = (2 ^ n) ^ 2) {g : SL(3, K)} (hg : g ∈ QZs K)
    {X : HMod n K} (hX : X ∈ V2z n K) :
    mat (rho hK g X) 0 0 = mat X 0 0 +
      ((g : Matrix (Fin 3) (Fin 3) K) 0 1 * bar n (mat X 0 1) +
        mat X 0 1 * bar n ((g : Matrix (Fin 3) (Fin 3) K) 0 1)) +
      ((g : Matrix (Fin 3) (Fin 3) K) 0 2 * bar n (mat X 0 2) +
        mat X 0 2 * bar n ((g : Matrix (Fin 3) (Fin 3) K) 0 2)) := by
  have hb : hermBlkZ X = 0 := mem_V2z_iff_hermBlkZ.1 hX
  rw [rhoZ_corner hK (QZs_le_perfZ hg), hb]
  simp [Fin.sum_univ_two]
  ring

theorem card_V1z (hK : Nat.card K = (2 ^ 1) ^ 2) : Nat.card ↥(V1z 1 K) = 2 := by
  have hbar : ∀ x : K, bar 1 x = x ^ 2 := fun x => by
    rw [CFSG.Quasithin.H.SU3.bar_apply, pow_one]
  have hsq : ∀ x : K, x ^ 2 = x → x = 0 ∨ x = 1 := fun x h => by
    have hx : x * (x - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hx with h' | h'
    · exact Or.inl h'
    · exact Or.inr (sub_eq_zero.mp h')
  have hH : (conjM 1 (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : K)))ᵀ =
      Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjM, Matrix.single_apply]
  have hE : mkH (n := 1) (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : K)) hH ∈ V1z 1 K := by
    intro i j hij
    have hij' : ¬ (0 = i ∧ 0 = j) := fun h => hij ⟨h.1.symm, h.2.symm⟩
    rw [mat_mkH]
    simp [Matrix.single_apply, hij']
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨mkH (n := 1) (Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : K)) hH, hE⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun z : ↥(V1z 1 K) => mat (z : HMod 1 K) 0 0) h
    simp [mat_one, mat_mkH] at this
  · ext X
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have ha : mat (X : HMod 1 K) 0 0 = 0 ∨ mat (X : HMod 1 K) 0 0 = 1 := by
      have h := herm_apply (X : HMod 1 K) 0 0
      rw [hbar] at h
      exact hsq _ h
    rcases ha with h0 | h1
    · left
      apply Subtype.ext
      show (X : HMod 1 K) = 1
      apply mat_injective
      ext i j
      rw [mat_one]
      by_cases hij : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := hij
        exact h0
      · rw [X.2 i j hij]
        rfl
    · right
      apply Subtype.ext
      apply mat_injective
      ext i j
      rw [mat_mkH]
      by_cases hij : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := hij
        simpa using h1
      · have hij' : ¬ (0 = i ∧ 0 = j) := fun h => hij ⟨h.1.symm, h.2.symm⟩
        rw [X.2 i j hij]
        simp [Matrix.single_apply, hij']

theorem rk_V1z (hK : Nat.card K = (2 ^ 1) ^ 2) : rk ↥(V1z 1 K) = 1 := by
  unfold rk
  rw [card_V1z hK]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat_self

end CFSG.Quasithin.RonanH46
