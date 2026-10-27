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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148R

open scoped Matrix

private theorem exists_cols {F : Type} [Field F] (e₁ e₂ e₃ : Fin 3 → F) :
    ∃ P : Matrix (Fin 3) (Fin 3) F, ∀ c : Fin 3 → F,
      P *ᵥ c = c 0 • e₁ + c 1 • e₂ + c 2 • e₃ := by
  refine ⟨Matrix.of fun i j => ![e₁, e₂, e₃] j i, fun c => ?_⟩
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

private theorem isUnit_det_of_cols {F : Type} [Field F] (P : Matrix (Fin 3) (Fin 3) F)
    (e₁ e₂ e₃ : Fin 3 → F)
    (hind : ∀ a b c : F, a • e₁ + b • e₂ + c • e₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hcol : ∀ c : Fin 3 → F, P *ᵥ c = c 0 • e₁ + c 1 • e₂ + c 2 • e₃) :
    IsUnit P.det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  rw [hcol] at hMv
  obtain ⟨h0, h1, h2⟩ := hind _ _ _ hMv
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem decomp_of_indep {F : Type} [Field F] (e₁ e₂ e₃ : Fin 3 → F)
    (hind : ∀ a b c : F, a • e₁ + b • e₂ + c • e₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (x : Fin 3 → F) : ∃ a b c : F, x = a • e₁ + b • e₂ + c • e₃ := by
  obtain ⟨P, hcol⟩ := exists_cols e₁ e₂ e₃
  have hdet : IsUnit P.det := isUnit_det_of_cols P e₁ e₂ e₃ hind hcol
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → F, P *ᵥ c = x :=
    ⟨P⁻¹ *ᵥ x, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hdet, Matrix.one_mulVec]⟩
  exact ⟨c 0, c 1, c 2, by rw [← hc, hcol]⟩

private theorem exists_mulVec_ne_zero_of_ne {F : Type} [Field F] {M : Matrix (Fin 3) (Fin 3) F}
    (hM : M ≠ 0) : ∃ v : Fin 3 → F, M *ᵥ v ≠ 0 := by
  by_contra h
  push Not at h
  apply hM
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

private theorem upper_of_entries {F : Type} [Field F] (M : Matrix (Fin 3) (Fin 3) F)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0) (h21 : M 2 1 = 0) :
    ∀ i j : Fin 3, j < i → M i j = 0 := by
  intro i j hji
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd hji (by decide)
    | exact h10
    | exact h20
    | exact h21

private theorem triangular_of_mulVec {F : Type} [Field F] (P : Matrix (Fin 3) (Fin 3) F)
    (hP : IsUnit P.det) (e₁ e₂ e₃ : Fin 3 → F)
    (hcol : ∀ c : Fin 3 → F, P *ᵥ c = c 0 • e₁ + c 1 • e₂ + c 2 • e₃)
    (y : Matrix (Fin 3) (Fin 3) F) (α β γ : F)
    (h1 : y *ᵥ e₁ = α • e₁) (h2 : y *ᵥ e₂ = β • e₁ + γ • e₂) :
    ∀ i j : Fin 3, j < i → (P⁻¹ * y * P) i j = 0 := by
  have hinv : ∀ x : Fin 3 → F, P⁻¹ *ᵥ (P *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec]
  have hM : ∀ x : Fin 3 → F, (P⁻¹ * y * P) *ᵥ x = P⁻¹ *ᵥ (y *ᵥ (P *ᵥ x)) := fun x => by
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  have hP0 : P *ᵥ Pi.single 0 1 = e₁ := by
    rw [hcol]
    simp [Pi.single_apply]
  have hP1 : P *ᵥ Pi.single 1 1 = e₂ := by
    rw [hcol]
    simp [Pi.single_apply]
  have hentry : ∀ i j : Fin 3, (P⁻¹ * y * P) i j = ((P⁻¹ * y * P) *ᵥ Pi.single j 1) i := by
    intro i j
    simp [Matrix.mulVec_single_one]
  have hc0 : (P⁻¹ * y * P) *ᵥ Pi.single 0 1 = α • Pi.single 0 1 := by
    rw [hM, hP0, h1, Matrix.mulVec_smul, ← hP0, hinv]
  have hc1 : (P⁻¹ * y * P) *ᵥ Pi.single 1 1 = β • Pi.single 0 1 + γ • Pi.single 1 1 := by
    rw [hM, hP1, h2, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ← hP0, ← hP1,
      hinv, hinv]
  have h10 : (P⁻¹ * y * P) 1 0 = 0 := by
    rw [hentry 1 0, hc0]
    simp [Pi.single_apply]
  have h20 : (P⁻¹ * y * P) 2 0 = 0 := by
    rw [hentry 2 0, hc0]
    simp [Pi.single_apply]
  have h21 : (P⁻¹ * y * P) 2 1 = 0 := by
    rw [hentry 2 1, hc1]
    simp [Pi.single_apply]
  exact upper_of_entries _ h10 h20 h21

private theorem exists_gl_of_indep {F : Type} [Field F] {N : Matrix (Fin 3) (Fin 3) F}
    (e₁ e₂ e₃ : Fin 3 → F)
    (hind : ∀ a b c : F, a • e₁ + b • e₂ + c • e₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hcomm : ∀ y : Matrix (Fin 3) (Fin 3) F, y * N = N * y →
      (∃ α : F, y *ᵥ e₁ = α • e₁) ∧ (∃ β γ : F, y *ᵥ e₂ = β • e₁ + γ • e₂)) :
    ∃ P : GL (Fin 3) F, ∀ y : Matrix (Fin 3) (Fin 3) F, y * N = N * y →
      ∀ i j : Fin 3, j < i →
        (((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * y * (P : Matrix (Fin 3) (Fin 3) F))
          i j = 0 := by
  obtain ⟨P, hcol⟩ := exists_cols e₁ e₂ e₃
  have hdet : IsUnit P.det := isUnit_det_of_cols P e₁ e₂ e₃ hind hcol
  refine ⟨⟨P, P⁻¹, Matrix.mul_nonsing_inv P hdet, Matrix.nonsing_inv_mul P hdet⟩,
    fun y hy i j hji => ?_⟩
  obtain ⟨⟨α, h1⟩, ⟨β, γ, h2⟩⟩ := hcomm y hy
  exact triangular_of_mulVec P hdet e₁ e₂ e₃ hcol y α β γ h1 h2 i j hji

theorem exists_triangularizing_of_nilpotent {F : Type} [Field F]
    {N : Matrix (Fin 3) (Fin 3) F} (hN0 : N ≠ 0) (hN3 : N ^ 3 = 0) :
    ∃ P : GL (Fin 3) F, ∀ y : Matrix (Fin 3) (Fin 3) F, y * N = N * y →
      ∀ i j : Fin 3, j < i →
        (((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * y * (P : Matrix (Fin 3) (Fin 3) F))
          i j = 0 := by
  by_cases hN2 : N ^ 2 = 0
  ·
    obtain ⟨v, hv⟩ := exists_mulVec_ne_zero_of_ne hN0
    have hNN : ∀ x : Fin 3 → F, N *ᵥ (N *ᵥ x) = 0 := fun x => by
      rw [Matrix.mulVec_mulVec, ← sq, hN2, Matrix.zero_mulVec]
    obtain ⟨w, hwK, hwS⟩ : ∃ w : Fin 3 → F, N *ᵥ w = 0 ∧ w ∉ Submodule.span F {N *ᵥ v} := by
      by_contra hcon
      push Not at hcon
      have hRK : LinearMap.range (Matrix.toLin' N) ≤ LinearMap.ker (Matrix.toLin' N) := by
        rintro _ ⟨x, rfl⟩
        exact LinearMap.mem_ker.2 (by simpa only [Matrix.toLin'_apply] using hNN x)
      have hkerle : LinearMap.ker (Matrix.toLin' N) ≤ Submodule.span F {N *ᵥ v} := by
        intro x hx
        exact hcon x (by simpa only [LinearMap.mem_ker, Matrix.toLin'_apply] using hx)
      have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' N)
      rw [Module.finrank_fin_fun] at hrn
      have h1 : Module.finrank F (Submodule.span F {N *ᵥ v}) = 1 := finrank_span_singleton hv
      have hle : Module.finrank F (LinearMap.range (Matrix.toLin' N)) ≤
          Module.finrank F (LinearMap.ker (Matrix.toLin' N)) := Submodule.finrank_mono hRK
      have hle2 : Module.finrank F (LinearMap.ker (Matrix.toLin' N)) ≤
          Module.finrank F (Submodule.span F {N *ᵥ v}) := Submodule.finrank_mono hkerle
      omega
    have hind : ∀ a b c : F, a • (N *ᵥ v) + b • w + c • v = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
      intro a b c habc
      have hc : c = 0 := by
        have h := congrArg (fun x => N *ᵥ x) habc
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hNN, hwK,
          smul_zero, add_zero, zero_add] at h
        exact (smul_eq_zero.1 h).resolve_right hv
      subst hc
      simp only [zero_smul, add_zero] at habc
      have hb : b = 0 := by
        by_contra hb
        apply hwS
        have hbw : b • w = -(a • (N *ᵥ v)) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact habc
        rw [show w = b⁻¹ • (b • w) from (inv_smul_smul₀ hb w).symm, hbw]
        exact (Submodule.span F {N *ᵥ v}).smul_mem _
          ((Submodule.span F {N *ᵥ v}).neg_mem
            ((Submodule.span F {N *ᵥ v}).smul_mem _ (Submodule.mem_span_singleton_self _)))
      subst hb
      simp only [zero_smul, add_zero] at habc
      exact ⟨(smul_eq_zero.1 habc).resolve_right hv, rfl, rfl⟩
    refine exists_gl_of_indep (N *ᵥ v) w v hind (fun y hy => ?_)
    have hc1 : ∀ x : Fin 3 → F, y *ᵥ (N *ᵥ x) = N *ᵥ (y *ᵥ x) := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hy]
    obtain ⟨a₀, b₀, c₀, hyv⟩ := decomp_of_indep (N *ᵥ v) w v hind (y *ᵥ v)
    obtain ⟨p, q, r, hyw⟩ := decomp_of_indep (N *ᵥ v) w v hind (y *ᵥ w)
    have hr : r = 0 := by
      have h : N *ᵥ (y *ᵥ w) = 0 := by rw [← hc1, hwK, Matrix.mulVec_zero]
      rw [hyw] at h
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hNN, hwK, smul_zero,
        add_zero, zero_add] at h
      exact (smul_eq_zero.1 h).resolve_right hv
    refine ⟨⟨c₀, ?_⟩, ⟨p, q, ?_⟩⟩
    · rw [hc1, hyv]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNN, hwK, Matrix.mulVec_zero, smul_zero,
        add_zero, zero_add]
    · rw [hyw, hr, zero_smul, add_zero]
  ·
    obtain ⟨v, hv⟩ := exists_mulVec_ne_zero_of_ne hN2
    have h22 : N ^ 2 * N ^ 2 = 0 := by
      rw [← pow_add]
      show N ^ (3 + 1) = 0
      rw [pow_succ, hN3, zero_mul]
    have h21 : N ^ 2 * N = 0 := by
      rw [← pow_succ]
      exact hN3
    have h12 : N * N ^ 2 = 0 := by
      rw [← pow_succ']
      exact hN3
    have hA : N ^ 2 *ᵥ (N ^ 2 *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, h22, Matrix.zero_mulVec]
    have hB : N ^ 2 *ᵥ (N *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, h21, Matrix.zero_mulVec]
    have hC : N *ᵥ (N ^ 2 *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, h12, Matrix.zero_mulVec]
    have hD : N *ᵥ (N *ᵥ v) = N ^ 2 *ᵥ v := by
      rw [Matrix.mulVec_mulVec, sq]
    have hind : ∀ a b c : F, a • (N ^ 2 *ᵥ v) + b • (N *ᵥ v) + c • v = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 := by
      intro a b c habc
      have hc : c = 0 := by
        have h := congrArg (fun x => N ^ 2 *ᵥ x) habc
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hA, hB, smul_zero,
          add_zero, zero_add] at h
        exact (smul_eq_zero.1 h).resolve_right hv
      subst hc
      simp only [zero_smul, add_zero] at habc
      have hb : b = 0 := by
        have h := congrArg (fun x => N *ᵥ x) habc
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_zero, hC, hD, smul_zero,
          add_zero, zero_add] at h
        exact (smul_eq_zero.1 h).resolve_right hv
      subst hb
      simp only [zero_smul, add_zero] at habc
      exact ⟨(smul_eq_zero.1 habc).resolve_right hv, rfl, rfl⟩
    refine exists_gl_of_indep (N ^ 2 *ᵥ v) (N *ᵥ v) v hind (fun y hy => ?_)
    have hyc : Commute y N := hy
    have hc2 : ∀ x : Fin 3 → F, y *ᵥ (N ^ 2 *ᵥ x) = N ^ 2 *ᵥ (y *ᵥ x) := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hyc.pow_right 2).eq]
    have hc1 : ∀ x : Fin 3 → F, y *ᵥ (N *ᵥ x) = N *ᵥ (y *ᵥ x) := fun x => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hy]
    obtain ⟨a₀, b₀, c₀, hyv⟩ := decomp_of_indep (N ^ 2 *ᵥ v) (N *ᵥ v) v hind (y *ᵥ v)
    refine ⟨⟨c₀, ?_⟩, ⟨b₀, c₀, ?_⟩⟩
    · rw [hc2, hyv]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hA, hB, smul_zero, add_zero, zero_add]
    · rw [hc1, hyv]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hC, hD, smul_zero, add_zero, zero_add]

end CFSG.RankThree.PartTwo.Sec14.Ronan148R

end
