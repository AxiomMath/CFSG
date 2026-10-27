module

public import CFSG.RankThree.SteinbergR3EUnitaryBlockDescent

public section

namespace CFSG.RankThree.SU4Rigidity

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.UnitaryBlock
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open scoped MatrixGroups

theorem su4_root_subgroup_and_linear_graph_pointwise_rigidity {k : Type*} [Field k] [Finite k]
    {q : ℕ} (hq : Nat.card k = q) {Ω : Type*} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] :
    Subgroup.centralizer (unitarySet (Ω := Ω) q 4) =
        (GeneralLinearGroup.scalar (Fin 4)).range ∧
      (¬ ∃ A : GL (Fin 4) Ω, ∀ X ∈ unitarySet (Ω := Ω) q 4,
        (A : Matrix (Fin 4) (Fin 4) Ω) * ((X : Matrix (Fin 4) (Fin 4) Ω)⁻¹)ᵀ *
          (↑A⁻¹ : Matrix (Fin 4) (Fin 4) Ω) = X) ∧
      ∃ C : SL(2, Ω), ∀ Y : SL(2, k),
        Matrix.SpecialLinearGroup.toGL ((blockSL Ω 2 2 C : SL(4, Ω)) *
          blockSL Ω 2 2 (Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y) *
            (blockSL Ω 2 2 C)⁻¹) ∈ unitarySet (Ω := Ω) q 4 := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hq2 : 2 ≤ q := by
    rw [← hq]
    exact Finite.one_lt_card
  refine ⟨centralizer_unitary_eq_range_scalar hq (by norm_num), ?_, ?_⟩
  ·
    rintro ⟨A, hA⟩
    have hq0 : (q : Ω) = 0 := by
      rw [← hq, Nat.card_eq_fintype_card, ← map_natCast (algebraMap k Ω),
        FiniteField.cast_card_eq_zero, map_zero]
    have : NeZero ((q + 1 : ℕ) : Ω) := ⟨by rw [Nat.cast_add, hq0, zero_add, Nat.cast_one]; simp⟩
    obtain ⟨t, ht⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q + 1)
    have htq : t ^ (q + 1) = 1 := ht.pow_eq_one
    have ht2 : t ^ 2 ≠ 1 := ht.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)
    have ht0 : t ≠ 0 := fun h => by
      rw [h, zero_pow (by omega)] at htq
      exact zero_ne_one htq
    set d : Fin 4 → Ω := ![t, t, t⁻¹ ^ 2, 1] with hd
    have hdpow : ∀ i, d i ^ (q + 1) = 1 := by
      have h3 : (t⁻¹ ^ 2) ^ (q + 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, inv_pow, htq, inv_one, one_pow]
      intro i
      fin_cases i
      · exact htq
      · exact htq
      · exact h3
      · exact one_pow _
    have hprod : ∏ i, d i = 1 := by
      rw [Fin.prod_univ_four]
      simp [d]
      field_simp
    have hdet : IsUnit (diagonal d).det := by
      rw [det_diagonal, hprod]
      exact isUnit_one
    have hX := hA _ (diagonal_mem_unitary (by omega) hdpow hprod hdet)
    change (A : Matrix (Fin 4) (Fin 4) Ω) * ((diagonal d)⁻¹)ᵀ *
      (↑A⁻¹ : Matrix (Fin 4) (Fin 4) Ω) = diagonal d at hX
    set d' : Fin 4 → Ω := ![t⁻¹, t⁻¹, t ^ 2, 1] with hd'
    have hinv : (diagonal d)⁻¹ = diagonal d' := by
      apply Matrix.inv_eq_left_inv
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [d, d', ht0]
    have htr := congrArg Matrix.trace hX
    rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, hinv, diagonal_transpose,
      trace_diagonal, trace_diagonal, Fin.sum_univ_four, Fin.sum_univ_four] at htr
    simp only [d, d'] at htr
    simp at htr
    have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    have key : (t - 1) ^ 3 * (t + 1) = 0 := by
      linear_combination t ^ 2 * htr + (1 + t * t⁻¹ - 2 * t) * hti
    apply ht2
    rcases mul_eq_zero.mp key with h | h
    · have : t = 1 := sub_eq_zero.mp ((pow_eq_zero_iff (n := 3) (by norm_num)).mp h)
      rw [this, one_pow]
    · have : t = -1 := eq_neg_of_add_eq_zero_left h
      rw [this]
      norm_num
  ·
    obtain ⟨ℓ, -, n, hℓ, hn⟩ := FiniteField.card' k
    have hkq : Nat.card k = ℓ ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    obtain rfl : q = ℓ ^ (n : ℕ) := hq.symm.trans hkq
    obtain ⟨C, hC⟩ := exists_blockSL_conj_mem_unitarySet (Ω := Ω) hℓ n.pos hkq
    refine ⟨C⁻¹, fun Y => ?_⟩
    have hJ : (blockSL Ω 2 2 C⁻¹ : SL(4, Ω)) *
        blockSL Ω 2 2 (Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y) *
          (blockSL Ω 2 2 C⁻¹)⁻¹ =
        blockSL Ω 2 2 (C⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * C) := by
      simp only [map_mul, map_inv, inv_inv]
    rw [hJ]
    exact hC 2 Y

end CFSG.RankThree.SU4Rigidity
