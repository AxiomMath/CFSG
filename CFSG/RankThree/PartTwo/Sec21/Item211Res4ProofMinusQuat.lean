module

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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res4Proof

open Matrix

section Quat

variable {R : Type*} [CommRing R]

theorem quat_e1 {U V : Matrix (Fin 2) (Fin 2) R} (hU : U * U = -1) : U * (U * V) = -V := by
  rw [← Matrix.mul_assoc, hU, Matrix.neg_mul, Matrix.one_mul]

theorem quat_e2 {U V : Matrix (Fin 2) (Fin 2) R} (hU : U * U = -1) (hUV : U * V = -(V * U)) :
    U * V * U = V := by
  have hVU : V * U = -(U * V) := by rw [hUV, neg_neg]
  rw [Matrix.mul_assoc, hVU, Matrix.mul_neg, ← Matrix.mul_assoc, hU, Matrix.neg_mul,
    Matrix.one_mul, neg_neg]

theorem quat_e3 {U V : Matrix (Fin 2) (Fin 2) R} (hU : U * U = -1) (hV : V * V = -1)
    (hUV : U * V = -(V * U)) : U * V * (U * V) = -1 := by
  have hVU : V * U = -(U * V) := by rw [hUV, neg_neg]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, hVU, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.mul_assoc, hV, ← Matrix.mul_assoc, hU]
  simp

theorem quat_e4 {U V : Matrix (Fin 2) (Fin 2) R} (hV : V * V = -1) (hUV : U * V = -(V * U)) :
    V * (U * V) = U := by
  have hVU : V * U = -(U * V) := by rw [hUV, neg_neg]
  rw [← Matrix.mul_assoc, hVU, Matrix.neg_mul, Matrix.mul_assoc, hV]
  simp

theorem psi_mul_self {a c : R} (hac : a * a + c * c = -1) {U V : Matrix (Fin 2) (Fin 2) R}
    (hU : U * U = -1) (hV : V * V = -1) (hUV : U * V = -(V * U)) :
    (a • U + c • (U * V)) * (a • U + c • (U * V)) = 1 := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  rw [hU, quat_e1 hU, quat_e2 hU hUV, quat_e3 hU hV hUV]
  have key : (a * a + c * c) • (-1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
    rw [hac, neg_one_smul, neg_neg]
  conv_rhs => rw [← key]
  module

theorem psi_mul_V {a c : R} {U V : Matrix (Fin 2) (Fin 2) R} (hV : V * V = -1)
    (hUV : U * V = -(V * U)) :
    (a • U + c • (U * V)) * V = -(V * (a • U + c • (U * V))) := by
  have hVU : V * U = -(U * V) := by rw [hUV, neg_neg]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  rw [Matrix.mul_assoc U V V, hV, quat_e4 hV hUV, hVU]
  simp only [Matrix.mul_neg, Matrix.mul_one, smul_neg, neg_add_rev, neg_neg]
  abel

theorem eq_psi_mul {a c : R} (hac : a * a + c * c = -1) {U V : Matrix (Fin 2) (Fin 2) R}
    (hV : V * V = -1) :
    U = (a • U + c • (U * V)) * (c • V - a • 1) := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]
  rw [Matrix.mul_assoc U V V, hV, Matrix.mul_neg, Matrix.mul_one]
  have : U = -((a * a + c * c) • U) := by
    rw [hac, neg_one_smul, neg_neg]
  conv_lhs => rw [this]
  module

theorem exists_quat_normal_form [IsDomain R] (hunit : ∀ r : R, r ≠ 0 → IsUnit r)
    (h2 : (2 : R) ≠ 0) {a c : R} (hac : a * a + c * c = -1) {U V : Matrix (Fin 2) (Fin 2) R}
    (hU : U * U = -1) (hV : V * V = -1) (hUV : U * V = -(V * U)) :
    ∃ P Pi : Matrix (Fin 2) (Fin 2) R, P * Pi = 1 ∧ Pi * P = 1 ∧
      U * Pi = Pi * !![-a, -c; -c, a] ∧ V * Pi = Pi * !![0, -1; 1, 0] := by
  set Ψ := a • U + c • (U * V) with hΨ
  have hΨ2 : Ψ * Ψ = 1 := psi_mul_self hac hU hV hUV
  have hΨV : Ψ * V = -(V * Ψ) := psi_mul_V hV hUV
  have hUΨ : U = Ψ * (c • V - a • 1) := eq_psi_mul hac hV
  have hcol : ∃ v : Fin 2 → R, (Ψ + 1) *ᵥ v ≠ 0 := by
    by_contra hall
    push Not at hall
    have hz : Ψ + 1 = 0 := by
      ext i j
      have := congrFun (hall (Pi.single j 1)) i
      simpa [Matrix.mulVec_single] using this
    have hΨn : Ψ = -1 := by rw [← sub_eq_zero, sub_neg_eq_add, hz]
    rw [hΨn, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg] at hΨV
    have hV0 : V = 0 := by
      have h2V : (2 : R) • V = 0 := by rw [two_smul]; nth_rw 1 [← hΨV]; exact neg_add_cancel V
      exact (smul_eq_zero.mp h2V).resolve_left h2
    rw [hV0, Matrix.zero_mul] at hV
    have := congrFun (congrFun hV 0) 0
    simp at this
  obtain ⟨v, hv⟩ := hcol
  set w := (Ψ + 1) *ᵥ v with hw
  have hΨw : Ψ *ᵥ w = w := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_add, hΨ2, Matrix.mul_one, add_comm]
  set y := V *ᵥ w with hy
  have hΨy : Ψ *ᵥ y = -y := by
    rw [hy, Matrix.mulVec_mulVec, hΨV, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hΨw]
  have hVy : V *ᵥ y = -w := by
    rw [hy, Matrix.mulVec_mulVec, hV, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hUw : U *ᵥ w = -a • w - c • y := by
    rw [hUΨ, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, ← hy, hΨy,
      hΨw]
    simp only [smul_neg, neg_smul]
    abel
  have hUy : U *ᵥ y = -c • w + a • y := by
    rw [hUΨ, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hVy,
      Matrix.mulVec_neg, hΨw, hΨy]
    simp only [smul_neg, neg_smul]
    abel
  have hPw : (Ψ + 1) *ᵥ w = (2 : R) • w := by
    rw [Matrix.add_mulVec, hΨw, Matrix.one_mulVec, two_smul]
  have hPy : (Ψ + 1) *ᵥ y = 0 := by
    rw [Matrix.add_mulVec, hΨy, Matrix.one_mulVec, neg_add_cancel]
  have hδ0 : w 0 * y 1 - y 0 * w 1 ≠ 0 := by
    intro h0
    have hr : ∀ i : Fin 2, y i • w = w i • y := by
      intro i
      funext k
      fin_cases i <;> fin_cases k <;> simp <;>
        first | ring1 | linear_combination h0 | linear_combination -h0
    have hyi : ∀ i : Fin 2, y i = 0 := by
      intro i
      have e := congrArg (fun x => (Ψ + 1) *ᵥ x) (hr i)
      simp only [Matrix.mulVec_smul, hPw, hPy, smul_zero] at e
      rw [smul_smul] at e
      rcases smul_eq_zero.mp e with h | h
      · exact (mul_eq_zero.mp h).resolve_right h2
      · exact absurd h hv
    have hy0 : y = 0 := funext fun i => hyi i
    apply hv
    have : w = -(V *ᵥ y) := by rw [hVy, neg_neg]
    rw [this, hy0, Matrix.mulVec_zero, neg_zero]
  obtain ⟨δu, hδu⟩ := hunit _ hδ0
  set Pi : Matrix (Fin 2) (Fin 2) R := !![w 0, y 0; w 1, y 1] with hPi
  set P : Matrix (Fin 2) (Fin 2) R :=
    ((δu⁻¹ : Rˣ) : R) • !![y 1, -y 0; -w 1, w 0] with hP
  have hinv : ((δu⁻¹ : Rˣ) : R) * (w 0 * y 1 - y 0 * w 1) = 1 := by rw [← hδu, Units.inv_mul]
  refine ⟨P, Pi, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, hPi, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hinv
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, hPi, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hinv
  · have h0 := congrFun hUw
    have h1 := congrFun hUy
    ext i j
    fin_cases i <;> fin_cases j
    · have := h0 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [hPi, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination this
    · have := h1 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [hPi, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination this
    · have := h0 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [hPi, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination this
    · have := h1 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [hPi, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination this
  · have h0 := congrFun hy
    have h1 := congrFun hVy
    ext i j
    fin_cases i <;> fin_cases j
    · have := h0 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [hPi, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -this
    · have := h1 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [hPi, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination this
    · have := h0 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [hPi, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -this
    · have := h1 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      simp [hPi, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination this

@[expose] def quatBlockU (a c : R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  fromBlocks ((-a) • 1) ((-c) • 1) ((-c) • 1) (a • 1)

@[expose] def quatBlockV : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  fromBlocks 0 (-1) 1 0

theorem quatBlockU_commute (a c : R) (Y : Matrix (Fin 2) (Fin 2) R) :
    fromBlocks Y 0 0 Y * quatBlockU a c = quatBlockU a c * fromBlocks Y 0 0 Y := by
  rw [quatBlockU, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem quatBlockV_commute (Y : Matrix (Fin 2) (Fin 2) R) :
    fromBlocks Y 0 0 Y * quatBlockV = quatBlockV * fromBlocks Y 0 0 Y := by
  rw [quatBlockV, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem eq_fromBlocks_of_commute_quat [IsDomain R] (h2 : (2 : R) ≠ 0) {a c : R}
    (hac : a * a + c * c = -1) {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hXU : X * quatBlockU a c = quatBlockU a c * X) (hXV : X * quatBlockV = quatBlockV * X) :
    X = fromBlocks X.toBlocks₁₁ 0 0 X.toBlocks₁₁ := by
  set A := X.toBlocks₁₁
  set B := X.toBlocks₁₂
  set C := X.toBlocks₂₁
  set D := X.toBlocks₂₂
  have hX : X = fromBlocks A B C D := (fromBlocks_toBlocks X).symm
  rw [hX, quatBlockV, fromBlocks_multiply, fromBlocks_multiply] at hXV
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.zero_mul, Matrix.one_mul,
    Matrix.neg_mul, add_zero, zero_add] at hXV
  obtain ⟨e1, e2, e3, -⟩ := Matrix.fromBlocks_inj.mp hXV
  have hDA : D = A := by rw [← e3]
  have hCB : C = -B := by rw [e1, neg_neg]
  rw [hX, quatBlockU, fromBlocks_multiply, fromBlocks_multiply] at hXU
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at hXU
  obtain ⟨f1, f2, -, -⟩ := Matrix.fromBlocks_inj.mp hXU
  rw [hCB] at f1
  rw [hDA] at f2
  have g1 := add_left_cancel f1
  simp only [neg_smul, smul_neg, neg_neg] at g1
  have hcB : c • B + c • B = 0 := neg_eq_iff_add_eq_zero.mp g1
  rw [add_comm ((-c) • A)] at f2
  have g2 := add_right_cancel f2
  simp only [neg_smul] at g2
  have haB : a • B + a • B = 0 := eq_neg_iff_add_eq_zero.mp g2
  rw [← two_smul R, smul_smul] at hcB haB
  have hB : B = 0 := by
    by_cases hc : c = 0
    · have ha : a ≠ 0 := by
        rintro rfl
        rw [hc] at hac
        simp at hac
      exact (smul_eq_zero.mp haB).resolve_left (mul_ne_zero h2 ha)
    · exact (smul_eq_zero.mp hcB).resolve_left (mul_ne_zero h2 hc)
  rw [hX, hB, hCB, hB, neg_zero, hDA]

theorem quat_sign_decomp {A : Type*} [Ring A] {u v g : A} (hu : u * u = -1) (hv : v * v = -1)
    (huv : u * v = -(v * u)) (hgu : g * u = u * g ∨ g * u = -(u * g))
    (hgv : g * v = v * g ∨ g * v = -(v * g)) :
    ∃ x x' : A, x * x' = 1 ∧ (x = 1 ∨ x = u ∨ x = v ∨ x = u * v) ∧
      x' * g * u = u * (x' * g) ∧ x' * g * v = v * (x' * g) := by
  have hvu : v * u = -(u * v) := by rw [huv, neg_neg]
  have hvuv : v * u * v = u := by
    rw [mul_assoc, huv, mul_neg, ← mul_assoc, hv, neg_one_mul, neg_neg]
  rcases hgu with hgu | hgu <;> rcases hgv with hgv | hgv
  · exact ⟨1, 1, by rw [one_mul], Or.inl rfl, by rw [one_mul, hgu], by rw [one_mul, hgv]⟩
  · refine ⟨u, -u, by rw [mul_neg, hu, neg_neg], Or.inr (Or.inl rfl), ?_, ?_⟩
    · rw [neg_mul, neg_mul, mul_assoc, hgu, ← mul_assoc, hu, mul_neg, ← mul_assoc, hu]
    · calc -u * g * v = -(u * (g * v)) := by rw [neg_mul, neg_mul, mul_assoc]
        _ = u * (v * g) := by rw [hgv, mul_neg, neg_neg]
        _ = v * (-u * g) := by rw [← mul_assoc, huv, neg_mul, neg_mul, mul_neg, mul_assoc]
  · refine ⟨v, -v, by rw [mul_neg, hv, neg_neg], Or.inr (Or.inr (Or.inl rfl)), ?_, ?_⟩
    · calc -v * g * u = -(v * (g * u)) := by rw [neg_mul, neg_mul, mul_assoc]
        _ = v * (u * g) := by rw [hgu, mul_neg, neg_neg]
        _ = u * (-v * g) := by rw [← mul_assoc, hvu, neg_mul, neg_mul, mul_neg, mul_assoc]
    · rw [neg_mul, neg_mul, mul_assoc, hgv, ← mul_assoc, hv, mul_neg, ← mul_assoc, hv]
  · refine ⟨u * v, v * u, ?_, Or.inr (Or.inr (Or.inr rfl)), ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc v, hv, neg_one_mul, mul_neg, hu, neg_neg]
    · calc v * u * g * u = v * u * (g * u) := by rw [mul_assoc]
        _ = -(v * (u * u) * g) := by rw [hgu, mul_neg]; simp only [mul_assoc]
        _ = v * g := by rw [hu]; simp
        _ = u * (v * u * g) := by
            rw [← mul_assoc, ← mul_assoc, huv, neg_mul, mul_assoc v u u, hu]
            simp
    · calc v * u * g * v = v * u * (g * v) := by rw [mul_assoc]
        _ = -(v * u * v * g) := by rw [hgv, mul_neg]; simp only [mul_assoc]
        _ = -(u * g) := by rw [hvuv]
        _ = v * (v * u * g) := by rw [← mul_assoc, ← mul_assoc, hv, neg_one_mul, neg_mul]

theorem quatBlockU_mul_self {a c : R} (hac : a * a + c * c = -1) :
    quatBlockU a c * quatBlockU a c = -1 := by
  rw [quatBlockU, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp only [smul_mul_smul_comm, Matrix.one_mul, ← add_smul]
  congr 1
  · rw [show -a * -a + -c * -c = a * a + c * c by ring, hac, neg_one_smul]
  · rw [show -a * -c + -c * a = 0 by ring, zero_smul, neg_zero]
  · rw [show -c * -a + a * -c = 0 by ring, zero_smul, neg_zero]
  · rw [show -c * -c + a * a = a * a + c * c by ring, hac, neg_one_smul]

theorem quatBlockV_mul_self : (quatBlockV : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
    quatBlockV = -1 := by
  rw [quatBlockV, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem quatBlockU_mul_V (a c : R) :
    quatBlockU a c * quatBlockV = -(quatBlockV * quatBlockU a c) := by
  rw [quatBlockU, quatBlockV, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg]
  simp

end Quat

end Item211Res4Proof

end CFSG.RankThree.PartTwo.Sec21
