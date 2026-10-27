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

private lemma l02qj2_omega_sq_add_omega_add_one {k : Type} [Field k] {ω : k} (hω : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [this, hω, sub_self]
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hω1
  · exact h1

private lemma l02qj2_three_ne_zero {k : Type} [Field k] {ω : k} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    (3 : k) ≠ 0 := by
  intro h3
  have hω2 : ω ^ 2 + ω + 1 = 0 := l02qj2_omega_sq_add_omega_add_one hω hω1
  have hsq : (ω - 1) ^ 2 = 0 := by
    calc (ω - 1) ^ 2 = ω ^ 2 + ω + 1 - 3 * ω := by ring
      _ = 0 - 3 * ω := by rw [hω2]
      _ = 0 := by rw [h3, zero_mul, sub_self]
  exact hω1 (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq))

private lemma l02qj2_exists_omega (k : Type) [Field k] [Finite k] (h3 : 3 ∣ Nat.card k - 1) :
    ∃ ω : kˣ, (ω : k) ^ 3 = 1 ∧ (ω : k) ≠ 1 := by
  haveI : Fintype k := Fintype.ofFinite k
  have hcard : Nat.card kˣ = Nat.card k - 1 := Nat.card_units k
  have hdvd : 3 ∣ Nat.card kˣ := by rw [hcard]; exact h3
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  refine ⟨ω, ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, show ω ^ 3 = 1 by rw [← hω, pow_orderOf_eq_one],
      Units.val_one]
  · intro h
    have h1 : ω = 1 := Units.ext h
    have hone : orderOf ω = 1 := by rw [h1]; exact orderOf_one
    rw [hω] at hone
    exact absurd hone (by norm_num)

private lemma l02qj2_pow_cube (k : Type) [Field k] [Finite k] (h3 : 3 ∣ Nat.card k - 1)
    (x : kˣ) (hx : x ^ ((Nat.card k - 1) / 3) = 1) : ∃ t : kˣ, t ^ 3 = x := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have hcard : Nat.card kˣ = Nat.card k - 1 := Nat.card_units k
  obtain ⟨ξ, hξ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have htop : Subgroup.zpowers ξ = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hξ]
  obtain ⟨i, hilt, hi⟩ : ∃ i, i < orderOf ξ ∧ ξ ^ i = x := by
    have hmem : x ∈ (Finset.range (orderOf ξ)).image (ξ ^ ·) := by
      rw [← mem_zpowers_iff_mem_range_orderOf, htop]
      exact Subgroup.mem_top x
    rw [Finset.mem_image] at hmem
    obtain ⟨i, hirange, hi⟩ := hmem
    exact ⟨i, Finset.mem_range.mp hirange, hi⟩
  have hm : orderOf ξ = Nat.card k - 1 := by rw [hξ, hcard]
  have hn3 : (Nat.card k - 1) / 3 * 3 = Nat.card k - 1 := Nat.div_mul_cancel h3
  have hn : 0 < (Nat.card k - 1) / 3 := by
    have hk2 : 2 ≤ Nat.card k := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  have hpow : ξ ^ (i * ((Nat.card k - 1) / 3)) = 1 := by
    rw [pow_mul, hi, hx]
  have hdvd0 : orderOf ξ ∣ i * ((Nat.card k - 1) / 3) :=
    (orderOf_dvd_iff_pow_eq_one (x := ξ) (n := i * ((Nat.card k - 1) / 3))).mpr hpow
  have hdvd : Nat.card k - 1 ∣ i * ((Nat.card k - 1) / 3) := by
    rwa [hm] at hdvd0
  have h3i : 3 ∣ i := by
    have hdvd' : (Nat.card k - 1) / 3 * 3 ∣ (Nat.card k - 1) / 3 * i := by
      rw [hn3, mul_comm ((Nat.card k - 1) / 3) i]
      exact hdvd
    exact (Nat.mul_dvd_mul_iff_left hn).mp hdvd'
  obtain ⟨j, hj⟩ := h3i
  refine ⟨ξ ^ j, ?_⟩
  rw [← pow_mul, mul_comm j 3, ← hj, hi]

private lemma l02qj2_case_cube (k : Type) [Field k] [Finite k] (h3 : 3 ∣ Nat.card k - 1)
    (g : GL (Fin 3) k)
    (hg : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (Matrix.GeneralLinearGroup.det g))
    (δ : kˣ) (hδ : δ ^ 3 = Matrix.GeneralLinearGroup.det g) (a : kˣ) :
    ∃ u : GL (Fin 3) k, u * g = g * u ∧ Matrix.GeneralLinearGroup.det u = a := by
  obtain ⟨ω, hω3, hω1⟩ := l02qj2_exists_omega k h3
  have hω2 : (ω : k) ^ 2 + (ω : k) + 1 = 0 := l02qj2_omega_sq_add_omega_add_one hω3 hω1
  have h3k : (3 : k) ≠ 0 := l02qj2_three_ne_zero hω3 hω1
  let g' : GL (Fin 3) k := Matrix.GeneralLinearGroup.scalar (Fin 3) δ⁻¹ * g
  have hg_eq : g = Matrix.GeneralLinearGroup.scalar (Fin 3) δ * g' := by
    show g = Matrix.GeneralLinearGroup.scalar (Fin 3) δ *
        (Matrix.GeneralLinearGroup.scalar (Fin 3) δ⁻¹ * g)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hg'3 : g' ^ 3 = 1 := by
    have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) δ⁻¹) g :=
      Matrix.GeneralLinearGroup.scalar_commute δ⁻¹ g
    calc g' ^ 3 = (Matrix.GeneralLinearGroup.scalar (Fin 3) δ⁻¹ * g) ^ 3 := rfl
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) δ⁻¹) ^ 3 * g ^ 3 := hcomm.mul_pow 3
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ((δ⁻¹) ^ 3) *
            Matrix.GeneralLinearGroup.scalar (Fin 3) (Matrix.GeneralLinearGroup.det g) := by
            rw [map_pow, hg]
      _ = 1 := by
            rw [← hδ, ← map_mul]
            rw [show (δ⁻¹) ^ 3 * δ ^ 3 = 1 by group, map_one]
  have hx : ((g' : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg'3, Units.val_one]
  obtain ⟨P, aIdx, hP⟩ :=
    CFSG.RankThree.PartTwo.Sec4.RonanK432.exists_diagonal_of_pow_three (n := 3) hω2 h3k hx
  let D : Matrix (Fin 3) (Fin 3) k := Matrix.diagonal (fun i => (ω : k) ^ (aIdx i).val)
  have hP' : (P : Matrix (Fin 3) (Fin 3) k) * (g' : Matrix (Fin 3) (Fin 3) k) *
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = D := by
    simpa only [D] using hP
  let Q : GL (Fin 3) k := P * g' * P⁻¹
  have hQmat : (Q : Matrix (Fin 3) (Fin 3) k) = D := by
    show (P : Matrix (Fin 3) (Fin 3) k) * (g' : Matrix (Fin 3) (Fin 3) k) *
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = D
    exact hP'
  have hPgP : P * g * P⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q := by
    rw [hg_eq]
    show P * (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * g') * P⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) δ * (P * g' * P⁻¹)
    rw [← mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute δ P]
    group
  have hg_conj : g = P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q) * P := by
    have h := congrArg (fun x : GL (Fin 3) k => P⁻¹ * x * P) hPgP
    have hL : P⁻¹ * (P * g * P⁻¹) * P = g := by group
    rw [hL] at h
    exact h
  let E : GL (Fin 3) k := Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal ![↑a, 1, 1]) (by
        rw [Matrix.det_diagonal, Fin.prod_univ_three]
        simp)
  have hEmat : (E : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal ![↑a, 1, 1] := by
    dsimp only [E]
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  have hEQ : E * Q = Q * E := by
    apply Units.ext
    show (E : Matrix (Fin 3) (Fin 3) k) * (Q : Matrix (Fin 3) (Fin 3) k) =
      (Q : Matrix (Fin 3) (Fin 3) k) * (E : Matrix (Fin 3) (Fin 3) k)
    rw [hQmat, hEmat, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hEs : E * Matrix.GeneralLinearGroup.scalar (Fin 3) δ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) δ * E :=
    (Matrix.GeneralLinearGroup.scalar_commute δ E).symm
  have hESQ : E * (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q) =
      (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q) * E := by
    calc E * (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q)
        = (E * Matrix.GeneralLinearGroup.scalar (Fin 3) δ) * Q :=
          (mul_assoc E (Matrix.GeneralLinearGroup.scalar (Fin 3) δ) Q).symm
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * E) * Q := by rw [hEs]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) δ * (E * Q) :=
          mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 3) δ) E Q
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) δ * (Q * E) := by rw [hEQ]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q) * E :=
          (mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin 3) δ) Q E).symm
  have huconj : (P⁻¹ * E * P) * (P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q) * P) =
      (P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q) * P) * (P⁻¹ * E * P) := by
    calc (P⁻¹ * E * P) * (P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q) * P)
        = P⁻¹ * (E * (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q)) * P := by group
      _ = P⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q) * E) * P := by rw [hESQ]
      _ = (P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 3) δ * Q) * P) * (P⁻¹ * E * P) := by
            group
  refine ⟨P⁻¹ * E * P, ?_, ?_⟩
  · rw [hg_conj]
    exact huconj
  · have hPmPi : (P : Matrix (Fin 3) (Fin 3) k) *
        ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
      show (P : Matrix (Fin 3) (Fin 3) k) *
        ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hdetPP : (P : Matrix (Fin 3) (Fin 3) k).det *
        ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det = 1 := by
      rw [← Matrix.det_mul, hPmPi, Matrix.det_one]
    have hPiPm : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det *
        (P : Matrix (Fin 3) (Fin 3) k).det = 1 := by
      rw [mul_comm, hdetPP]
    have hEmatdet : (Matrix.diagonal ![↑a, 1, 1] : Matrix (Fin 3) (Fin 3) k).det = (↑a : k) := by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp
    have huMat : ((P⁻¹ * E * P : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (E : Matrix (Fin 3) (Fin 3) k) *
        (P : Matrix (Fin 3) (Fin 3) k) := by
      rfl
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, huMat, hEmat]
    rw [Matrix.det_mul, Matrix.det_mul, hEmatdet]
    calc ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det * (↑a : k) *
          (P : Matrix (Fin 3) (Fin 3) k).det
        = (↑a : k) * (((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).det *
            (P : Matrix (Fin 3) (Fin 3) k).det) := by ring
      _ = (↑a : k) * 1 := by rw [hPiPm]
      _ = (↑a : k) := by rw [mul_one]

private lemma l02qj2_exists_zmod_three_pow_eq_units {k : Type} [Field k] {ω : kˣ}
    (hω : ((ω : k)) ^ 2 + (ω : k) + 1 = 0) (μ : kˣ) (hμ : μ ^ 3 = 1) :
    ∃ kk : ZMod 3, ω ^ kk.val = μ := by
  have hμk : (μ : k) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hμ, Units.val_one]
  obtain ⟨kk, hkk⟩ := CFSG.RankThree.PartTwo.Sec4.RonanK432.exists_zmod_three_pow_eq hω hμk
  refine ⟨kk, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hkk]

private lemma l02qj2_case_not_cube (k : Type) [Field k] [Finite k] (h3 : 3 ∣ Nat.card k - 1)
    (g : GL (Fin 3) k) (d : kˣ) (hdg : d = Matrix.GeneralLinearGroup.det g)
    (hd : ∀ c : kˣ, c ^ 3 ≠ d) (a : kˣ) :
    ∃ u : GL (Fin 3) k, u * g = g * u ∧ Matrix.GeneralLinearGroup.det u = a := by
  have hn3 : (Nat.card k - 1) / 3 * 3 = Nat.card k - 1 := Nat.div_mul_cancel h3
  have hdn : d ^ ((Nat.card k - 1) / 3) ≠ 1 := by
    intro h
    obtain ⟨t, ht⟩ := l02qj2_pow_cube k h3 d h
    exact hd t ht
  have hcard : Nat.card kˣ = Nat.card k - 1 := Nat.card_units k
  have hdn3 : (d ^ ((Nat.card k - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, hn3, ← hcard]
    exact pow_card_eq_one'
  have han3 : (a ^ ((Nat.card k - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, hn3, ← hcard]
    exact pow_card_eq_one'
  have hdn3k : ((d ^ ((Nat.card k - 1) / 3) : kˣ) : k) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hdn3, Units.val_one]
  have hdn1k : ((d ^ ((Nat.card k - 1) / 3) : kˣ) : k) ≠ 1 := by
    intro h
    exact hdn (Units.ext h)
  have hdn2 : ((d ^ ((Nat.card k - 1) / 3) : kˣ) : k) ^ 2 +
      ((d ^ ((Nat.card k - 1) / 3) : kˣ) : k) + 1 = 0 :=
    l02qj2_omega_sq_add_omega_add_one hdn3k hdn1k
  obtain ⟨kz, hkz⟩ :=
    l02qj2_exists_zmod_three_pow_eq_units hdn2 (a ^ ((Nat.card k - 1) / 3)) han3
  let e : ℕ := kz.val
  have he : e < 3 := ZMod.val_lt kz
  have hane : a ^ ((Nat.card k - 1) / 3) = (d ^ ((Nat.card k - 1) / 3)) ^ e := hkz.symm
  have hae : (a * (d ^ e)⁻¹) ^ ((Nat.card k - 1) / 3) = 1 := by
    rw [mul_pow, inv_pow, ← pow_mul, hane, ← pow_mul]
    rw [mul_comm e ((Nat.card k - 1) / 3), mul_inv_cancel]
  obtain ⟨t, ht⟩ := l02qj2_pow_cube k h3 (a * (d ^ e)⁻¹) hae
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) t * g ^ e, ?_, ?_⟩
  · calc (Matrix.GeneralLinearGroup.scalar (Fin 3) t * g ^ e) * g
        = Matrix.GeneralLinearGroup.scalar (Fin 3) t * (g ^ e * g) := by rw [mul_assoc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) t * g ^ (e + 1) := by rw [← pow_succ]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) t * (g * g ^ e) := by rw [pow_succ']
      _ = (Matrix.GeneralLinearGroup.scalar (Fin 3) t * g) * g ^ e := by rw [mul_assoc]
      _ = (g * Matrix.GeneralLinearGroup.scalar (Fin 3) t) * g ^ e := by
            rw [Matrix.GeneralLinearGroup.scalar_commute]
      _ = g * (Matrix.GeneralLinearGroup.scalar (Fin 3) t * g ^ e) := by rw [mul_assoc]
  · have hdet : Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin 3) t * g ^ e) = t ^ 3 * d ^ e := by
      rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, map_pow, hdg.symm]
      simp
    rw [hdet, ht]
    group

theorem kgLangT3_exists_centralizer_det (k : Type) [Field k] [Finite k]
    (h3 : 3 ∣ Nat.card k - 1) (g : GL (Fin 3) k)
    (hg : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) (Matrix.GeneralLinearGroup.det g))
    (a : kˣ) :
    ∃ u : GL (Fin 3) k, u * g = g * u ∧ Matrix.GeneralLinearGroup.det u = a := by
  by_cases hcube : ∃ δ : kˣ, δ ^ 3 = Matrix.GeneralLinearGroup.det g
  · obtain ⟨δ, hδ⟩ := hcube
    exact l02qj2_case_cube k h3 g hg δ hδ a
  · push Not at hcube
    exact l02qj2_case_not_cube k h3 g (Matrix.GeneralLinearGroup.det g) rfl hcube a

end CFSG.StandardType
