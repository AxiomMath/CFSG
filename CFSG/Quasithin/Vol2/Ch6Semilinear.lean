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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13

variable {F : Type} [Field F]

@[expose] def NormalizesSL2 (g : (Fin 2 → F) ≃+ (Fin 2 → F)) : Prop :=
  ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, ∃ B : Matrix.SpecialLinearGroup (Fin 2) F,
    ∀ v : Fin 2 → F, g ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
      (B : Matrix (Fin 2) (Fin 2) F).mulVec (g v)

@[expose] def sl2X (b : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2Y (c : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

theorem eq_smul_one_of_commute (N : Matrix (Fin 2) (Fin 2) F)
    (hX : N * (sl2X (1 : F) : Matrix (Fin 2) (Fin 2) F) =
      (sl2X (1 : F) : Matrix (Fin 2) (Fin 2) F) * N)
    (hY : N * (sl2Y (1 : F) : Matrix (Fin 2) (Fin 2) F) =
      (sl2Y (1 : F) : Matrix (Fin 2) (Fin 2) F) * N) :
    N = N 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hX' := congrFun₂ hX
  have hY' := congrFun₂ hY
  simp only [sl2X, sl2Y, Matrix.mul_apply, Fin.sum_univ_two] at hX' hY'
  have h10 : N 1 0 = 0 := by
    have := hX' 0 0
    simp at this
    linear_combination this
  have h01 : N 0 1 = 0 := by
    have := hY' 0 0
    simp at this
    linear_combination this
  have h11 : N 1 1 = N 0 0 := by
    have := hX' 0 1
    simp at this
    linear_combination -this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, h11]

theorem smul_eq_transvection_sum (a : F) (v : Fin 2 → F) :
    a • v = ((sl2X (1 : F) : Matrix (Fin 2) (Fin 2) F).mulVec
        ((sl2Y a : Matrix (Fin 2) (Fin 2) F).mulVec v - v) -
          ((sl2Y a : Matrix (Fin 2) (Fin 2) F).mulVec v - v)) +
      ((sl2Y a : Matrix (Fin 2) (Fin 2) F).mulVec
        ((sl2X (1 : F) : Matrix (Fin 2) (Fin 2) F).mulVec v - v) -
          ((sl2X (1 : F) : Matrix (Fin 2) (Fin 2) F).mulVec v - v)) := by
  have hX : ∀ w : Fin 2 → F,
      (sl2X (1 : F) : Matrix (Fin 2) (Fin 2) F).mulVec w = ![w 0 + w 1, w 1] := by
    intro w; funext i; fin_cases i <;> simp [sl2X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hY : ∀ w : Fin 2 → F,
      (sl2Y a : Matrix (Fin 2) (Fin 2) F).mulVec w = ![w 0, a * w 0 + w 1] := by
    intro w; funext i; fin_cases i <;> simp [sl2Y, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hX, hY, hX, hY]
  funext i
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]

theorem matrix_eq_of_mulVec_eq {B B' : Matrix (Fin 2) (Fin 2) F}
    (h : ∀ w : Fin 2 → F, B.mulVec w = B'.mulVec w) : B = B' := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

variable [Finite F]

namespace NormalizesSL2

variable {g : (Fin 2 → F) ≃+ (Fin 2 → F)}

theorem surj (hg : NormalizesSL2 g) (B : Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ v, g ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
        (B : Matrix (Fin 2) (Fin 2) F).mulVec (g v) := by
  classical
  choose ψ hψ using hg
  have hinj : Function.Injective ψ := by
    intro A A' h
    apply Subtype.ext
    apply matrix_eq_of_mulVec_eq
    intro v
    apply g.injective
    rw [hψ A v, hψ A' v, h]
  have : Finite (Matrix.SpecialLinearGroup (Fin 2) F) := inferInstance
  obtain ⟨A, hA⟩ := (Finite.injective_iff_surjective.mp hinj) B
  exact ⟨A, fun v => hA ▸ hψ A v⟩

theorem exists_matrix (hg : NormalizesSL2 g) (a : F) :
    ∃ N : Matrix (Fin 2) (Fin 2) F, (∀ v, g (a • v) = N.mulVec (g v)) ∧
      ∀ B : Matrix.SpecialLinearGroup (Fin 2) F,
        N * (B : Matrix (Fin 2) (Fin 2) F) = (B : Matrix (Fin 2) (Fin 2) F) * N := by
  obtain ⟨BX, hBX⟩ := hg (sl2X 1)
  obtain ⟨BY, hBY⟩ := hg (sl2Y a)
  set X : Matrix (Fin 2) (Fin 2) F := (BX : Matrix (Fin 2) (Fin 2) F)
  set Y : Matrix (Fin 2) (Fin 2) F := (BY : Matrix (Fin 2) (Fin 2) F)
  have hX1 : ∀ w, g ((sl2X (1 : F) : Matrix (Fin 2) (Fin 2) F).mulVec w - w) =
      (X - 1).mulVec (g w) := by
    intro w
    rw [map_sub, hBX, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hY1 : ∀ w, g ((sl2Y a : Matrix (Fin 2) (Fin 2) F).mulVec w - w) =
      (Y - 1).mulVec (g w) := by
    intro w
    rw [map_sub, hBY, Matrix.sub_mulVec, Matrix.one_mulVec]
  set N : Matrix (Fin 2) (Fin 2) F := (X - 1) * (Y - 1) + (Y - 1) * (X - 1)
  have hN : ∀ v, g (a • v) = N.mulVec (g v) := by
    intro v
    rw [smul_eq_transvection_sum a v, map_add, hX1, hY1, hY1, hX1, Matrix.add_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  refine ⟨N, hN, fun B => ?_⟩
  obtain ⟨A, hA⟩ := surj hg B
  apply matrix_eq_of_mulVec_eq
  intro w
  obtain ⟨v, rfl⟩ := g.surjective w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hA, ← hN, ← hN, ← hA]
  congr 1
  funext i
  simp [Matrix.mulVec_smul]

theorem exists_semilinear (hg : NormalizesSL2 g) :
    ∃ σ : F ≃+* F, ∀ (a : F) (v : Fin 2 → F), g (a • v) = σ a • g v := by
  classical
  choose N hN hNc using hg.exists_matrix
  have hscal : ∀ a, N a = N a 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := fun a =>
    eq_smul_one_of_commute (N a) (hNc a (sl2X 1)) (hNc a (sl2Y 1))
  let s : F → F := fun a => N a 0 0
  have hs : ∀ a v, g (a • v) = s a • g v := by
    intro a v
    rw [hN a v, hscal a, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin 2 → F, g v₀ ≠ 0 := by
    refine ⟨g.symm (Pi.single 0 1), ?_⟩
    simp
  have hsmul_inj : ∀ x y : F, x • g v₀ = y • g v₀ → x = y := by
    intro x y hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv₀
    have := congrFun hxy i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi
    exact mul_right_cancel₀ hi this
  have hone : s 1 = 1 := by
    apply hsmul_inj
    rw [← hs, one_smul, one_smul]
  have hadd : ∀ a b, s (a + b) = s a + s b := by
    intro a b
    apply hsmul_inj
    rw [← hs, add_smul, map_add, hs, hs, add_smul]
  have hmul : ∀ a b, s (a * b) = s a * s b := by
    intro a b
    apply hsmul_inj
    rw [← hs, mul_smul, hs, hs, mul_smul]
  let σ₀ : F →+* F :=
    { toFun := s
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have := hadd 0 0
        simp only [add_zero] at this
        linear_combination -this
      map_add' := hadd }
  have hbij : Function.Bijective σ₀ :=
    ⟨σ₀.injective, Finite.injective_iff_surjective.mp σ₀.injective⟩
  exact ⟨RingEquiv.ofBijective σ₀ hbij, fun a v => hs a v⟩

end NormalizesSL2

@[expose] def sl2D (a : F) (ha : a ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

omit [Finite F] in
theorem exists_eq_smul_of_commute (g : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hg : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F),
      g ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) = (A : Matrix (Fin 2) (Fin 2) F).mulVec (g v)) :
    ∃ c : F, ∀ v, g v = c • v := by
  have hX : ∀ w : Fin 2 → F,
      (sl2X (1 : F) : Matrix (Fin 2) (Fin 2) F).mulVec w = ![w 0 + w 1, w 1] := by
    intro w; funext i; fin_cases i <;> simp [sl2X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hY : ∀ w : Fin 2 → F,
      (sl2Y (1 : F) : Matrix (Fin 2) (Fin 2) F).mulVec w = ![w 0, w 0 + w 1] := by
    intro w; funext i; fin_cases i <;> simp [sl2Y, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hD : ∀ (a : F) (ha : a ≠ 0) (w : Fin 2 → F),
      (sl2D a ha : Matrix (Fin 2) (Fin 2) F).mulVec w = ![a * w 0, a⁻¹ * w 1] := by
    intro a ha w; funext i; fin_cases i <;> simp [sl2D, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  obtain ⟨w, hw⟩ : ∃ w, g ![1, 0] = w := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, g ![0, 1] = u := ⟨_, rfl⟩
  have hv0 : (![0, 0] : Fin 2 → F) = 0 := by funext i; fin_cases i <;> rfl
  have hw1 : w 1 = 0 := by
    have h := hg (sl2X 1) ![1, 0]
    simp only [hX, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, hw] at h
    have := congrFun h 0
    simp only [Matrix.cons_val_zero] at this
    linear_combination -this
  have hu0 : u 0 = 0 := by
    have h := hg (sl2Y 1) ![0, 1]
    simp only [hY, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, hu] at h
    have := congrFun h 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    linear_combination -this
  have hlm : w 0 = u 1 := by
    have h := hg (sl2X 1) ![0, 1]
    simp only [hX, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add,
      hu] at h
    have hsplit : (![1, 1] : Fin 2 → F) = ![1, 0] + ![0, 1] := by
      funext i; fin_cases i <;> simp
    rw [hsplit, map_add, hw, hu] at h
    have := congrFun h 0
    simp only [Pi.add_apply, Matrix.cons_val_zero, hu0, add_zero] at this
    linear_combination this
  have hx : ∀ x : F, g ![x, 0] = x • w := by
    intro x
    by_cases hx0 : x = 0
    · subst hx0
      rw [hv0, map_zero, zero_smul]
    · have h := hg (sl2D x hx0) ![1, 0]
      simp only [hD, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
        mul_zero, hw] at h
      rw [h]
      funext i; fin_cases i <;> simp [hw1]
  have hy : ∀ y : F, g ![0, y] = y • u := by
    intro y
    by_cases hy0 : y = 0
    · subst hy0
      rw [hv0, map_zero, zero_smul]
    · have h := hg (sl2D y⁻¹ (inv_ne_zero hy0)) ![0, 1]
      simp only [hD, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
        mul_zero, inv_inv, hu] at h
      rw [h]
      funext i; fin_cases i <;> simp [hu0]
  refine ⟨w 0, fun v => ?_⟩
  have hsplit : v = ![v 0, 0] + ![0, v 1] := by
    funext i; fin_cases i <;> simp
  rw [hsplit, map_add, hx, hy]
  funext i; fin_cases i <;> simp [hw1, hu0, hlm] <;> ring

end CFSG.Quasithin.H13
