module

import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddModel
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG.RankThree.PartTwo.Sec4 (PiField slPi glPi diagE)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

private def uniOfSqZero (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0) : GL (Fin 3) K :=
  ⟨1 + N, 1 - N, by simp [mul_add, add_mul, mul_sub, sub_mul, hN],
    by simp [mul_add, add_mul, mul_sub, sub_mul, hN]⟩

private theorem uni_pow_one_add (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + (n : K) • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, hN, smul_zero, add_zero,
      Nat.cast_succ, add_smul, one_smul]
    abel

private theorem uni_comm_diagE (N : Matrix (Fin 3) (Fin 3) K) (e : Kˣ)
    (h0 : ∀ j, N 0 j = 0) (h1 : ∀ i, N i 0 = 0) :
    (1 + N) * Matrix.diagonal ![(e : K), 1, 1] = Matrix.diagonal ![(e : K), 1, 1] * (1 + N) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal, Matrix.diagonal_mul, h0, h1]

private theorem uni_not_mem_statedScalars (U : GL (Fin 3) K)
    (h : (U : Matrix (Fin 3) (Fin 3) K) 1 2 ≠ 0) : U ∉ StatedScalars (Fin 3) K := by
  rintro hU
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hU
  apply h
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  simp

private theorem uni_of_sqZero (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0)
    (h0 : ∀ j, N 0 j = 0) (h1 : ∀ i, N i 0 = 0) (h12 : N 1 2 ≠ 0) (hp : (p : K) = 0) :
    ∃ U : GL (Fin 3) K, (U : Matrix (Fin 3) (Fin 3) K) = 1 + N ∧ U ∉ StatedScalars (Fin 3) K ∧
      U ^ p = 1 ∧ ∀ e : Kˣ, U * diagE e = diagE e * U := by
  refine ⟨uniOfSqZero N hN, rfl, uni_not_mem_statedScalars _ ?_, ?_, ?_⟩
  · show (1 + N) 1 2 ≠ 0
    rw [Matrix.add_apply, Matrix.one_apply_ne (by decide), zero_add]
    exact h12
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (1 + N) ^ p = 1
    rw [uni_pow_one_add N hN, hp, zero_smul, add_zero]
  · intro e
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Sec4.coe_diagE]
    exact uni_comm_diagE N e h0 h1

theorem exists_uni (hK : PiField π p f K) :
    ∃ U ∈ slPi π 3 (p ^ f) K, U ∉ StatedScalars (Fin 3) K ∧ U ^ p = 1 ∧
      ∀ e : Kˣ, U * diagE e = diagE e * U := by
  haveI : CharP K p := charP_of_piField hK
  have hp : (p : K) = 0 := CharP.cast_eq_zero K p
  cases π
  ·
    have h : UnitaryFieldData p f K := hK.unitary
    obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
    obtain ⟨t, ht0, hbt⟩ : ∃ t : K, t ≠ 0 ∧ h.bar t = -t :=
      ⟨c₀ - h.bar c₀, sub_ne_zero.mpr (Ne.symm hc₀), by rw [map_sub, h.bar_bar]; ring⟩
    have htt : h.bar (t * t) = t * t := by rw [map_mul, hbt, neg_mul_neg]
    obtain ⟨γ, hγ⟩ := h.normHom_surjective ⟨t * t, h.mem_fixedField.mpr htt⟩
    have hγ' : γ * h.bar γ = t * t := by
      have := congrArg Subtype.val hγ
      simpa [UnitaryFieldData.norm] using this
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      apply ht0
      simpa using hγ'.symm
    obtain ⟨N, hNdef⟩ : ∃ N : Matrix (Fin 3) (Fin 3) K,
        N = !![0, 0, 0; 0, t, γ; 0, -h.bar γ, -t] := ⟨_, rfl⟩
    have hN : N * N = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hNdef, Matrix.mul_apply, Fin.sum_univ_three] <;>
        first | ring1 | linear_combination hγ' | linear_combination (-1 : K) * hγ'
    have h0 : ∀ j, N 0 j = 0 := by
      intro j
      fin_cases j <;> simp [hNdef]
    have h1 : ∀ i, N i 0 = 0 := by
      intro i
      fin_cases i <;> simp [hNdef]
    have h12 : N 1 2 ≠ 0 := by simpa [hNdef] using hγ0
    obtain ⟨U, hU, hU1, hU2, hU3⟩ := uni_of_sqZero N hN h0 h1 h12 hp
    refine ⟨U, ?_, hU1, hU2, hU3⟩
    rw [Sec4.mem_slPi_false h]
    constructor
    · rw [hU, Matrix.det_fin_three]
      simp [hNdef]
      first | ring1 | linear_combination hγ' | linear_combination (-1 : K) * hγ'
    · rw [hU]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hNdef, Matrix.mul_apply, Fin.sum_univ_three, hbt, h.bar_bar] <;>
        first | ring1 | linear_combination hγ' | linear_combination (-1 : K) * hγ'
  ·
    obtain ⟨N, hNdef⟩ : ∃ N : Matrix (Fin 3) (Fin 3) K,
        N = !![0, 0, 0; 0, 0, 1; 0, 0, 0] := ⟨_, rfl⟩
    have hN : N * N = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hNdef, Matrix.mul_apply, Fin.sum_univ_three]
    have h0 : ∀ j, N 0 j = 0 := by
      intro j
      fin_cases j <;> simp [hNdef]
    have h1 : ∀ i, N i 0 = 0 := by
      intro i
      fin_cases i <;> simp [hNdef]
    have h12 : N 1 2 ≠ 0 := by simp [hNdef]
    obtain ⟨U, hU, hU1, hU2, hU3⟩ := uni_of_sqZero N hN h0 h1 h12 hp
    refine ⟨U, ?_, hU1, hU2, hU3⟩
    rw [Sec4.mem_slPi_true, hU, Matrix.det_fin_three]
    simp [hNdef]

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
