module

import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.StandardType

private lemma triD4Line_omega_sq_add_omega_add_one {k : Type} [Field k] {ω : k} (hω : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [this, hω, sub_self]
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hω1
  · exact h1

private lemma triD4Line_three_ne_zero {k : Type} [Field k] {ω : k} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (3 : k) ≠ 0 := by
  intro h3
  have hω2 : ω ^ 2 + ω + 1 = 0 := triD4Line_omega_sq_add_omega_add_one hω hω1
  have hsq : (ω - 1) ^ 2 = 0 := by
    calc (ω - 1) ^ 2 = ω ^ 2 + ω + 1 - 3 * ω := by ring
      _ = 0 - 3 * ω := by rw [hω2]
      _ = 0 := by rw [h3, zero_mul, sub_self]
  exact hω1 (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq))

private lemma triD4Line_zmod3_injective_of_sum_zero (a : Fin 3 → ZMod 3)
    (hsum : ∑ i, a i = 0) (hne : ∃ i j, a i ≠ a j) : Function.Injective a := by
  revert a
  decide +kernel

private def triD4Line_idxOf (a : Fin 3 → ZMod 3) (i : Fin 3) : Fin 3 :=
  ⟨(a i).val, ZMod.val_lt (a i)⟩

theorem triD4Line_exists_conj_diagonal (k : Type) [Field k] (ω : k) (hω : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (g : Matrix (Fin 3) (Fin 3) k) (hg : g ^ 3 = 1) (hdet : g.det = 1)
    (hgs : ∀ μ : k, g ≠ Matrix.scalar (Fin 3) μ) :
    ∃ h : Matrix (Fin 3) (Fin 3) k, h.det = 1 ∧ h * g = Matrix.diagonal ![1, ω, ω ^ 2] * h := by
  have hω2 : ω ^ 2 + ω + 1 = 0 := triD4Line_omega_sq_add_omega_add_one hω hω1
  have h3 : (3 : k) ≠ 0 := triD4Line_three_ne_zero hω hω1
  have hωpr : IsPrimitiveRoot ω 3 :=
    CFSG.RankThree.PartTwo.Sec4.RonanK432.isPrimitiveRoot_three_of_sq_add_add_one hω2 h3
  obtain ⟨M, a, hM⟩ :=
    CFSG.RankThree.PartTwo.Sec4.RonanK432.exists_diagonal_of_pow_three (n := 3) hω2 h3 hg
  let A : Matrix (Fin 3) (Fin 3) k := (M : Matrix (Fin 3) (Fin 3) k)
  let B : Matrix (Fin 3) (Fin 3) k :=
    ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
  let d : Fin 3 → k := fun i => ω ^ (a i).val
  have hM' : A * g * B = Matrix.diagonal d := hM
  have hAB : A * B = 1 := by
    show (M : Matrix (Fin 3) (Fin 3) k) *
      ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : B * A = 1 := by
    show ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      (M : Matrix (Fin 3) (Fin 3) k) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet_diag : (Matrix.diagonal d).det = 1 := by
    calc (Matrix.diagonal d).det = A.det * g.det * B.det := by
          rw [← hM', Matrix.det_mul, Matrix.det_mul]
      _ = A.det * B.det := by rw [hdet, mul_one]
      _ = 1 := by rw [← Matrix.det_mul, hAB]; simp
  have hprod : ∏ i, d i = 1 := by
    rw [← Matrix.det_diagonal]
    exact hdet_diag
  have hpow : ω ^ (∑ i, (a i).val) = 1 := by
    rw [← Finset.prod_pow_eq_pow_sum Finset.univ (fun i => (a i).val) ω]
    simpa [d] using hprod
  have hdvd : 3 ∣ ∑ i, (a i).val := (hωpr.pow_eq_one_iff_dvd _).mp hpow
  have hsum : ∑ i, a i = 0 := by
    have h1 : ((∑ i, (a i).val : ℕ) : ZMod 3) = 0 :=
      (ZMod.natCast_eq_zero_iff _ 3).mpr hdvd
    rw [← h1, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun i _ => (ZMod.natCast_zmod_val (a i)).symm)
  have hne : ∃ i j, a i ≠ a j := by
    by_contra h
    push Not at h
    have hdconst : d = fun _ => ω ^ (a 0).val := by
      funext i
      simp [d, h i 0]
    have hscalar_smul : Matrix.scalar (Fin 3) (ω ^ (a 0).val) =
        (ω ^ (a 0).val) • (1 : Matrix (Fin 3) (Fin 3) k) := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    have hg_scalar : g = Matrix.scalar (Fin 3) (ω ^ (a 0).val) := by
      calc g = B * (A * g * B) * A := by
            rw [show B * (A * g * B) * A = (B * A) * g * (B * A) by noncomm_ring,
              hBA, Matrix.one_mul, Matrix.mul_one]
        _ = B * Matrix.scalar (Fin 3) (ω ^ (a 0).val) * A := by
            rw [hM', hdconst, Matrix.scalar_apply]
        _ = B * ((ω ^ (a 0).val) • (1 : Matrix (Fin 3) (Fin 3) k)) * A := by
            rw [hscalar_smul]
        _ = (ω ^ (a 0).val) • (B * A) := by
            simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = (ω ^ (a 0).val) • (1 : Matrix (Fin 3) (Fin 3) k) := by rw [hBA]
        _ = Matrix.scalar (Fin 3) (ω ^ (a 0).val) := hscalar_smul.symm
    exact hgs _ hg_scalar
  have hinj : Function.Injective a := triD4Line_zmod3_injective_of_sum_zero a hsum hne
  have hψinj : Function.Injective (triD4Line_idxOf a) := by
    intro i j hij
    apply hinj
    exact ZMod.val_injective 3 (congrArg Fin.val hij)
  let ψ : Fin 3 → Fin 3 := triD4Line_idxOf a
  let P : Matrix (Fin 3) (Fin 3) k := fun i j => if i = ψ j then 1 else 0
  let Q : Matrix (Fin 3) (Fin 3) k := fun i j => if j = ψ i then 1 else 0
  let Dfun : Fin 3 → k := fun i => ω ^ (i : ℕ)
  let Dmat : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal Dfun
  have hDψ : ∀ j, d j = Dfun (ψ j) := by
    intro j
    simp [d, Dfun, ψ, triD4Line_idxOf]
  have hQP : Q * P = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (ψ i)]
    · by_cases hij : i = j
      · simp [P, Q, hij]
      · have hne' : ψ i ≠ ψ j := fun hh => hij (hψinj hh)
        simp [P, Q, hij, hne']
    · intro m _ hm
      simp [Q, hm]
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  have hPdiag : P * Matrix.diagonal d = Dmat * P := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = ψ j
    · subst hij
      simp [P, Dmat, Dfun, hDψ j]
    · simp [P, hij]
  have hAg : A * g = Matrix.diagonal d * A := by
    calc A * g = A * g * (B * A) := by rw [hBA, Matrix.mul_one]
      _ = (A * g * B) * A := by noncomm_ring
      _ = Matrix.diagonal d * A := by rw [hM']
  have hh0 : (P * A) * g = Dmat * (P * A) := by
    calc (P * A) * g = P * (A * g) := by rw [Matrix.mul_assoc]
      _ = P * (Matrix.diagonal d * A) := by rw [hAg]
      _ = (P * Matrix.diagonal d) * A := by rw [Matrix.mul_assoc]
      _ = (Dmat * P) * A := by rw [hPdiag]
      _ = Dmat * (P * A) := by rw [Matrix.mul_assoc]
  have hdetP : P.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hQP
  have hdetA : A.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hBA
  have hdet0 : (P * A).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hdetP hdetA
  have hDvec : Dfun = ![1, ω, ω ^ 2] := by
    funext i
    fin_cases i <;> simp [Dfun]
  have hDmat : Dmat = Matrix.diagonal ![1, ω, ω ^ 2] := by
    show Matrix.diagonal Dfun = Matrix.diagonal ![1, ω, ω ^ 2]
    rw [hDvec]
  refine ⟨Matrix.diagonal ![(P * A).det⁻¹, 1, 1] * (P * A), ?_, ?_⟩
  · have hdiagdet : (Matrix.diagonal ![(P * A).det⁻¹, 1, 1]).det = (P * A).det⁻¹ := by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp
    rw [Matrix.det_mul, hdiagdet, inv_mul_cancel₀ hdet0]
  · have hED : Matrix.diagonal ![(P * A).det⁻¹, 1, 1] * Dmat =
        Dmat * Matrix.diagonal ![(P * A).det⁻¹, 1, 1] := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    calc Matrix.diagonal ![(P * A).det⁻¹, 1, 1] * (P * A) * g
        = Matrix.diagonal ![(P * A).det⁻¹, 1, 1] * ((P * A) * g) := by
          rw [Matrix.mul_assoc]
      _ = Matrix.diagonal ![(P * A).det⁻¹, 1, 1] * (Dmat * (P * A)) := by rw [hh0]
      _ = (Matrix.diagonal ![(P * A).det⁻¹, 1, 1] * Dmat) * (P * A) := by
          rw [Matrix.mul_assoc]
      _ = (Dmat * Matrix.diagonal ![(P * A).det⁻¹, 1, 1]) * (P * A) := by rw [hED]
      _ = Dmat * (Matrix.diagonal ![(P * A).det⁻¹, 1, 1] * (P * A)) := by
          rw [Matrix.mul_assoc]
      _ = Matrix.diagonal ![1, ω, ω ^ 2] *
            (Matrix.diagonal ![(P * A).det⁻¹, 1, 1] * (P * A)) := by rw [hDmat]

end CFSG.StandardType
