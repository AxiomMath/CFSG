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

namespace CFSG.Quasithin

open scoped Matrix

namespace D37Lift

variable {R : Type*} [CommRing R]

theorem colDecomp {d r : ℕ} (M : Matrix (Fin d) (Fin r) R) :
    M = ∑ j, Matrix.vecMulVec (M.col j) (Pi.single j 1 : Fin r → R) := by
  ext a b
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.col]

theorem eq_one_of_mulVec_eq_self {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ w : Fin n → R, M *ᵥ w = w) : M = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simp only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_apply] at this
  rw [this, Matrix.one_apply, Pi.single_apply]

theorem exists_mulVec_ne_self {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (h : M ≠ 1) :
    ∃ w : Fin n → R, M *ᵥ w ≠ w := by
  by_contra hcon
  exact h (eq_one_of_mulVec_eq_self M fun w => by_contra fun hw => hcon ⟨w, hw⟩)

theorem mulVec_sub_self {G : Type*} [Group G] {n : ℕ}
    (T : G →* Matrix.GeneralLinearGroup (Fin n) R) (g h : G) (w : Fin n → R) :
    (T g : Matrix (Fin n) (Fin n) R) *ᵥ ((T h : Matrix (Fin n) (Fin n) R) *ᵥ w - w) =
      ((T (g * h) : Matrix (Fin n) (Fin n) R) *ᵥ w - w) -
        ((T g : Matrix (Fin n) (Fin n) R) *ᵥ w - w) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, map_mul, Units.val_mul]
  abel

theorem span_sub_eq_top {G : Type*} [Group G] {n : ℕ}
    (T : G →* Matrix.GeneralLinearGroup (Fin n) R)
    (irr : ∀ W : Submodule R (Fin n → R),
      (∀ g : G, ∀ w ∈ W, (T g : Matrix (Fin n) (Fin n) R) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (nt : ∃ g, T g ≠ 1) :
    Submodule.span R {u : Fin n → R | ∃ (g : G) (w : Fin n → R),
      u = (T g : Matrix (Fin n) (Fin n) R) *ᵥ w - w} = ⊤ := by
  set S := Submodule.span R {u : Fin n → R | ∃ (g : G) (w : Fin n → R),
      u = (T g : Matrix (Fin n) (Fin n) R) *ᵥ w - w} with hS
  have hinv : ∀ g : G, ∀ u ∈ S, (T g : Matrix (Fin n) (Fin n) R) *ᵥ u ∈ S := by
    intro g u hu
    have hle : S ≤ S.comap (Matrix.mulVecLin (T g : Matrix (Fin n) (Fin n) R)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, w, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, mulVec_sub_self]
      exact S.sub_mem (Submodule.subset_span ⟨g * h, w, rfl⟩) (Submodule.subset_span ⟨g, w, rfl⟩)
    exact hle hu
  rcases irr S hinv with h | h
  · exfalso
    obtain ⟨g, hg⟩ := nt
    have hg' : (T g : Matrix (Fin n) (Fin n) R) ≠ 1 := fun h1 => hg (Units.ext h1)
    obtain ⟨w, hw⟩ := exists_mulVec_ne_self _ hg'
    have hmem : (T g : Matrix (Fin n) (Fin n) R) *ᵥ w - w ∈ S := Submodule.subset_span ⟨g, w, rfl⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hw hmem
  · exact h

theorem closure_sub_eq_top {G : Type*} [Group G] {n : ℕ}
    (T : G →* Matrix.GeneralLinearGroup (Fin n) R)
    (irr : ∀ W : AddSubgroup (Fin n → R),
      (∀ g : G, ∀ w ∈ W, (T g : Matrix (Fin n) (Fin n) R) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (nt : ∃ g, T g ≠ 1) :
    AddSubgroup.closure {u : Fin n → R | ∃ (g : G) (w : Fin n → R),
      u = (T g : Matrix (Fin n) (Fin n) R) *ᵥ w - w} = ⊤ := by
  set S := AddSubgroup.closure {u : Fin n → R | ∃ (g : G) (w : Fin n → R),
      u = (T g : Matrix (Fin n) (Fin n) R) *ᵥ w - w} with hS
  have hinv : ∀ g : G, ∀ u ∈ S, (T g : Matrix (Fin n) (Fin n) R) *ᵥ u ∈ S := by
    intro g u hu
    have hle : S ≤ S.comap (Matrix.mulVecLin (T g : Matrix (Fin n) (Fin n) R)).toAddMonoidHom := by
      refine AddSubgroup.closure_le _ |>.2 ?_
      rintro _ ⟨h, w, rfl⟩
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show (T g : Matrix (Fin n) (Fin n) R) *ᵥ _ ∈ S
      rw [mulVec_sub_self]
      exact S.sub_mem (AddSubgroup.subset_closure ⟨g * h, w, rfl⟩)
        (AddSubgroup.subset_closure ⟨g, w, rfl⟩)
    exact hle hu
  rcases irr S hinv with h | h
  · exfalso
    obtain ⟨g, hg⟩ := nt
    have hg' : (T g : Matrix (Fin n) (Fin n) R) ≠ 1 := fun h1 => hg (Units.ext h1)
    obtain ⟨w, hw⟩ := exists_mulVec_ne_self _ hg'
    have hmem : (T g : Matrix (Fin n) (Fin n) R) *ᵥ w - w ∈ S :=
      AddSubgroup.subset_closure ⟨g, w, rfl⟩
    rw [h, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    exact hw hmem
  · exact h

end D37Lift

end CFSG.Quasithin
