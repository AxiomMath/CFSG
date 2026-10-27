module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofU4Mat
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item21Early3Proof

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU

variable {n : ℕ} {K : Type} [Field K]

theorem coe_diagU_conj (b : Fin 4 → Kˣ) (g : GL (Fin 4) K) (i j : Fin 4) :
    ((diagU b * g * (diagU b)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
      (b i : K) * (g : Matrix (Fin 4) (Fin 4) K) i j * ((b j : K))⁻¹ := by
  have hinv : (((diagU b)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal fun k => ((b k : K))⁻¹ := by
    rw [← diagU_inv_val]
  rw [Units.val_mul, Units.val_mul, hinv, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  where
    diagU_inv_val : (((diagU b)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        Matrix.diagonal fun k => ((b k : K))⁻¹ := by
      rw [show (diagU b)⁻¹ = diagU b⁻¹ from
        inv_eq_of_mul_eq_one_right (by rw [diagU_mul, mul_inv_cancel, diagU_one]), diagU_val]
      congr 1
      funext k
      simp

theorem herm_of_involution (hU : UnitaryFieldData 2 n K) {v : GL (Fin 4) K}
    (hvU : v ∈ unitarySU 2 n K 4) (hv : v * v = 1) (i j : Fin 4) :
    hU.bar ((v : Matrix (Fin 4) (Fin 4) K) j i) = (v : Matrix (Fin 4) (Fin 4) K) i j := by
  obtain ⟨-, hunit⟩ := (mem_unitarySU_iff hU).mp hvU
  have hvv : (v : Matrix (Fin 4) (Fin 4) K) * (v : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, hv, Units.val_one]
  have h : ((v : Matrix (Fin 4) (Fin 4) K).map hU.bar)ᵀ = (v : Matrix (Fin 4) (Fin 4) K) := by
    calc ((v : Matrix (Fin 4) (Fin 4) K).map hU.bar)ᵀ =
        ((v : Matrix (Fin 4) (Fin 4) K).map hU.bar)ᵀ *
          ((v : Matrix (Fin 4) (Fin 4) K) * (v : Matrix (Fin 4) (Fin 4) K)) := by
          rw [hvv, Matrix.mul_one]
      _ = (((v : Matrix (Fin 4) (Fin 4) K).map hU.bar)ᵀ * (v : Matrix (Fin 4) (Fin 4) K)) *
          (v : Matrix (Fin 4) (Fin 4) K) := by rw [Matrix.mul_assoc]
      _ = (v : Matrix (Fin 4) (Fin 4) K) := by rw [hunit, Matrix.one_mul]
  have := congrFun (congrFun h i) j
  simpa using this

theorem matHyp_of_involution (hU : UnitaryFieldData 2 n K) {v : GL (Fin 4) K}
    (hvU : v ∈ unitarySU 2 n K 4) (hv : v * v = 1) {a b : Fin 4 → Kˣ} (hb : ∀ i, b i ^ 3 = 1)
    (hfv : diagU a * v = v * diagU a)
    (hvw : v * (diagU b * v * (diagU b)⁻¹) = diagU b * v * (diagU b)⁻¹ * v) :
    have := hU.charP
    MatHyp hU.bar ((v : Matrix (Fin 4) (Fin 4) K) - 1) (fun i => (a i : K))
      (fun i => (b i : K)) := by
  have := hU.charP
  set M := (v : Matrix (Fin 4) (Fin 4) K) with hM
  have hvv : M * M = 1 := by rw [hM, ← Units.val_mul, hv, Units.val_one]
  refine ⟨fun i => by rw [← Units.val_pow_eq_pow_val, hb i, Units.val_one], ?_, ?_, ?_, ?_⟩
  ·
    intro i j
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, herm_of_involution hU hvU hv i j]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.one_apply_ne (Ne.symm hij), Matrix.one_apply_ne hij, map_zero]
  ·
    intro i j
    have hX : (M - 1) * (M - 1) = 0 := by
      have : (M - 1) * (M - 1) = M * M - M - M + 1 := by
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
          Matrix.one_mul]
        abel
      rw [this, hvv]
      ext k l
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination ((1 : Matrix (Fin 4) (Fin 4) K) k l - M k l) * h2
    have := congrFun (congrFun hX i) j
    simpa [Matrix.mul_apply] using this
  ·
    intro i j hij
    have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K)) hfv) i) j
    simp only [Units.val_mul, diagU_val, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    have hne : i ≠ j := fun e => hij (by rw [e])
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    have h2 : ((a i : K) - (a j : K)) * M i j = 0 := by
      rw [hM]
      linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hij
    · exact h3
  ·
    intro i j
    set Dm : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal fun k => (b k : K) with hDm
    set Dinv : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal fun k => ((b k : K))⁻¹ with hDinv
    have hDD : Dm * Dinv = 1 := by
      rw [hDm, hDinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      exact mul_inv_cancel₀ (b k).ne_zero
    have hW : ((diagU b * v * (diagU b)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        Dm * M * Dinv := by
      ext k l
      rw [coe_diagU_conj, hDm, hDinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    have h1 : M * (Dm * M * Dinv) = (Dm * M * Dinv) * M := by
      have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hvw
      simp only [Units.val_mul] at this
      rw [← Units.val_mul, ← Units.val_mul, hW] at this
      rw [← hM] at this
      exact this
    have h2 : (M - 1) * (Dm * (M - 1) * Dinv) = (Dm * (M - 1) * Dinv) * (M - 1) := by
      have e : Dm * (M - 1) * Dinv = Dm * M * Dinv - 1 := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hDD]
      rw [e]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, h1]
      abel
    have h3 := congrFun (congrFun h2 i) j
    rw [Matrix.mul_apply, Matrix.mul_apply] at h3
    simp only [hDm, hDinv, Matrix.mul_diagonal, Matrix.diagonal_mul] at h3
    exact h3

theorem conj_eq_of_torus (hU : UnitaryFieldData 2 n K) {f e v : GL (Fin 4) K}
    (hf : f ∈ torusSU 3 4 K) (he : e ∈ torusSU 3 4 K) (hf1 : f ≠ 1)
    (hvU : v ∈ unitarySU 2 n K 4) (hv : v * v = 1) (hfv : f * v = v * f)
    (hvw : v * (e * v * e⁻¹) = e * v * e⁻¹ * v) : e * v * e⁻¹ = v := by
  have := hU.charP
  obtain ⟨a, ha3, ha1, rfl⟩ := mem_torusSU_iff.mp hf
  obtain ⟨b, hb3, -, rfl⟩ := mem_torusSU_iff.mp he
  have hM := matHyp_of_involution hU hvU hv hb3 hfv hvw
  have hnc : ∃ i j, (a i : K) ≠ (a j : K) := by
    by_contra hall
    push Not at hall
    apply hf1
    have hai : ∀ i, a i = a 0 := fun i => Units.ext (hall i 0)
    have h4 : a 0 ^ 4 = 1 := by
      have : ∏ i, a i = a 0 ^ 4 := by
        rw [Fin.prod_univ_four, hai 1, hai 2, hai 3]
        simp only [pow_succ, pow_zero, one_mul]
      rw [← this, ha1]
    have h0 : a 0 = 1 := by
      have := ha3 0
      calc a 0 = a 0 ^ 4 * (a 0 ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4, this, inv_one, mul_one]
    have : a = 1 := funext fun i => by rw [hai i, h0]; rfl
    rw [this, diagU_one]
  apply Units.ext
  ext i j
  rw [coe_diagU_conj]
  by_cases hbij : (b i : K) = (b j : K)
  · rw [hbij, mul_comm, ← mul_assoc, inv_mul_cancel₀ (b j).ne_zero, one_mul]
  · have h0 := eq_zero_of_ne hM hnc hbij
    have hne : i ≠ j := fun e => hbij (by rw [e])
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h0
    rw [h0, mul_zero, zero_mul]

end Item21Early3Proof

end CFSG.RankThree.PartTwo.Sec21
