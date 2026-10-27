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

open scoped Matrix

namespace CFSG.ASVolI.ChH

@[expose] def sixPermVec (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun i => x (σ⁻¹ i)

@[expose] def sixToFive (x : Fin 6 → ZMod 2) : Fin 5 → ZMod 2 :=
  fun i => x i.castSucc + x 5

private def sixToFiveLin : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) where
  toFun := sixToFive
  map_add' x y := by
    funext i
    simp only [sixToFive, Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [sixToFive, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private def sixExt : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun y := ![y 0, y 1, y 2, y 3, y 4, 0]
  map_add' x y := by
    funext k
    fin_cases k <;> simp
  map_smul' c x := by
    funext k
    fin_cases k <;> simp

private def sixCoordSum : (Fin 5 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun y := ∑ i, y i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

private def sixPermVecLin (σ : Equiv.Perm (Fin 6)) :
    (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (σ⁻¹ : Equiv.Perm (Fin 6))

private theorem sixToFiveLin_apply (x : Fin 6 → ZMod 2) : sixToFiveLin x = sixToFive x := rfl

private theorem sixPermVecLin_apply (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) :
    sixPermVecLin σ x = sixPermVec σ x := rfl

private def sixOnesFive : Fin 5 → ZMod 2 := fun _ => 1

private def sixOnesSix : Fin 6 → ZMod 2 := fun _ => 1

private def sixLastBasis : Fin 6 → ZMod 2 := Pi.single 5 1

private theorem sixPermVecLin_ones (σ : Equiv.Perm (Fin 6)) :
    sixPermVecLin σ sixOnesSix = sixOnesSix := rfl

private theorem sixToFiveLin_ones : sixToFiveLin sixOnesSix = 0 := by decide +kernel

private theorem sixExt_sixToFiveLin :
    ∀ x : Fin 6 → ZMod 2, sixExt (sixToFiveLin x) = x + x 5 • sixOnesSix := by
  decide +kernel

private theorem sixExt_ones : sixExt sixOnesFive = sixOnesSix + sixLastBasis := by
  decide +kernel

private theorem sixCoordSum_sixToFiveLin :
    ∀ x : Fin 6 → ZMod 2, sixCoordSum (sixToFiveLin x) = ∑ i, x i := by
  decide +kernel

private theorem sum_sixExt : ∀ y : Fin 5 → ZMod 2, ∑ i, sixExt y i = sixCoordSum y := by
  decide +kernel

private theorem sixCoordSum_ones : sixCoordSum sixOnesFive = 1 := by decide +kernel

private theorem sum_sixLastBasis : ∑ i, sixLastBasis i = 1 := by decide +kernel

private theorem sum_sixPermVecLin (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) :
    ∑ i, sixPermVecLin σ x i = ∑ i, x i :=
  Equiv.sum_comp σ⁻¹ x

private theorem sixPermVecLin_mul (σ τ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) :
    sixPermVecLin (σ * τ) x = sixPermVecLin σ (sixPermVecLin τ x) := by
  funext i
  simp [sixPermVecLin_apply, sixPermVec, mul_inv_rev]

private def sixCorrection (σ : Equiv.Perm (Fin 6)) : Fin 5 → ZMod 2 :=
  sixOnesFive + sixToFiveLin (sixPermVecLin σ sixLastBasis)

private def sixAction (σ : Equiv.Perm (Fin 6)) :
    (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
  sixToFiveLin ∘ₗ sixPermVecLin σ ∘ₗ sixExt + sixCoordSum.smulRight (sixCorrection σ)

private theorem sixAction_apply (σ : Equiv.Perm (Fin 6)) (y : Fin 5 → ZMod 2) :
    sixAction σ y = sixToFiveLin (sixPermVecLin σ (sixExt y)) + sixCoordSum y • sixCorrection σ :=
  rfl

private theorem sixToFiveLin_perm_ext_sixToFiveLin (σ : Equiv.Perm (Fin 6))
    (x : Fin 6 → ZMod 2) :
    sixToFiveLin (sixPermVecLin σ (sixExt (sixToFiveLin x))) =
      sixToFiveLin (sixPermVecLin σ x) := by
  rw [sixExt_sixToFiveLin x]
  simp only [map_add, map_smul, sixPermVecLin_ones, sixToFiveLin_ones, smul_zero, add_zero]

private theorem sixToFiveLin_perm_ext_correction (σ τ : Equiv.Perm (Fin 6)) :
    sixToFiveLin (sixPermVecLin σ (sixExt (sixCorrection τ))) =
      sixToFiveLin (sixPermVecLin σ sixLastBasis) +
        sixToFiveLin (sixPermVecLin (σ * τ) sixLastBasis) := by
  unfold sixCorrection
  simp only [map_add, sixExt_ones, sixPermVecLin_ones, sixToFiveLin_ones,
    sixToFiveLin_perm_ext_sixToFiveLin, sixPermVecLin_mul, zero_add]

private theorem sixCoordSum_correction (τ : Equiv.Perm (Fin 6)) :
    sixCoordSum (sixCorrection τ) = 0 := by
  unfold sixCorrection
  rw [map_add, sixCoordSum_ones, sixCoordSum_sixToFiveLin, sum_sixPermVecLin, sum_sixLastBasis]
  decide

private theorem sixCoordSum_sixAction (τ : Equiv.Perm (Fin 6)) (y : Fin 5 → ZMod 2) :
    sixCoordSum (sixAction τ y) = sixCoordSum y := by
  rw [sixAction_apply, map_add, map_smul, sixCoordSum_sixToFiveLin, sum_sixPermVecLin, sum_sixExt,
    sixCoordSum_correction]
  simp

private theorem sixAction_mul (σ τ : Equiv.Perm (Fin 6)) :
    sixAction (σ * τ) = sixAction σ * sixAction τ := by
  refine LinearMap.ext fun y => ?_
  have h : ∀ a b o : Fin 5 → ZMod 2, a + b + (o + a) = o + b := by
    intro a b o
    funext i
    simp only [Pi.add_apply]
    generalize a i = p
    generalize b i = q
    generalize o i = r
    revert p q r
    decide
  rw [Module.End.mul_apply, sixAction_apply σ (sixAction τ y), sixCoordSum_sixAction,
    sixAction_apply τ y, sixAction_apply (σ * τ) y]
  simp only [map_add, map_smul, sixToFiveLin_perm_ext_sixToFiveLin,
    sixToFiveLin_perm_ext_correction]
  unfold sixCorrection
  rw [add_assoc, ← smul_add, sixPermVecLin_mul σ τ (sixExt y), h]

private theorem sixAction_one : sixAction 1 = 1 := by
  refine LinearMap.ext fun y => ?_
  show sixAction 1 y = y
  revert y
  decide +kernel

private def sixActionMatrix (σ : Equiv.Perm (Fin 6)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  LinearMap.toMatrix' (sixAction σ)

private theorem sixActionMatrix_mulVec (σ : Equiv.Perm (Fin 6)) (y : Fin 5 → ZMod 2) :
    sixActionMatrix σ *ᵥ y = sixAction σ y :=
  LinearMap.toMatrix'_mulVec _ _

private theorem sixActionMatrix_one : sixActionMatrix 1 = 1 := by
  unfold sixActionMatrix
  rw [sixAction_one]
  exact LinearMap.toMatrix'_one

private theorem sixActionMatrix_mul (σ τ : Equiv.Perm (Fin 6)) :
    sixActionMatrix (σ * τ) = sixActionMatrix σ * sixActionMatrix τ := by
  unfold sixActionMatrix
  rw [sixAction_mul]
  exact LinearMap.toMatrix'_mul _ _

private def sixActionHom : Equiv.Perm (Fin 6) →* Matrix (Fin 5) (Fin 5) (ZMod 2) where
  toFun := sixActionMatrix
  map_one' := sixActionMatrix_one
  map_mul' := sixActionMatrix_mul

private theorem sixActionMatrix_equivariant (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2)
    (hx : ∑ i, x i = 0) : sixToFive (sixPermVec σ x) = sixActionMatrix σ *ᵥ sixToFive x := by
  have h1 : sixActionMatrix σ *ᵥ sixToFive x = sixToFiveLin (sixPermVecLin σ x) := by
    rw [sixActionMatrix_mulVec, ← sixToFiveLin_apply x, sixAction_apply,
      sixToFiveLin_perm_ext_sixToFiveLin, sixCoordSum_sixToFiveLin, hx, zero_smul, add_zero]
  rw [h1]
  rfl

private theorem sixActionMatrix_orth_swap : ∀ x y : Fin 6, x ≠ y →
    sixActionMatrix (Equiv.swap x y) * (sixActionMatrix (Equiv.swap x y))ᵀ = 1 := by
  decide +kernel

private theorem sixActionMatrix_orth (σ : Equiv.Perm (Fin 6)) :
    sixActionMatrix σ * (sixActionMatrix σ)ᵀ = 1 := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [sixActionMatrix_one]; simp
  | swap_mul f x y hxy ih =>
    rw [sixActionMatrix_mul, Matrix.transpose_mul]
    calc sixActionMatrix (Equiv.swap x y) * sixActionMatrix f *
          ((sixActionMatrix f)ᵀ * (sixActionMatrix (Equiv.swap x y))ᵀ)
        = sixActionMatrix (Equiv.swap x y) * (sixActionMatrix f * (sixActionMatrix f)ᵀ) *
          (sixActionMatrix (Equiv.swap x y))ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ih, Matrix.mul_one]; exact sixActionMatrix_orth_swap x y hxy

private def sixTestVec (i : Fin 5) : Fin 6 → ZMod 2 := Pi.single i.castSucc 1 + Pi.single 5 1

private theorem sum_sixTestVec : ∀ i : Fin 5, ∑ k, sixTestVec i k = 0 := by
  decide +kernel

private theorem sixTestVec_pair : ∀ (u v : Fin 6) (j : Fin 5),
    (∀ i : Fin 5, sixTestVec i v + sixTestVec i u = sixTestVec i j.castSucc + sixTestVec i 5) →
    (u = 5 ∧ v = j.castSucc) ∨ (u = j.castSucc ∧ v = 5) := by
  decide +kernel

private theorem eq_one_of_fixes_sixTestVec (σ : Equiv.Perm (Fin 6))
    (h : ∀ i : Fin 5, sixToFive (sixPermVec σ (sixTestVec i)) = sixToFive (sixTestVec i)) :
    σ = 1 := by
  have hpair : ∀ j : Fin 5, (σ⁻¹ 5 = 5 ∧ σ⁻¹ j.castSucc = j.castSucc) ∨
      (σ⁻¹ 5 = j.castSucc ∧ σ⁻¹ j.castSucc = 5) := fun j =>
    sixTestVec_pair _ _ j fun i => congrFun (h i) j
  have h5 : σ⁻¹ 5 = 5 := by
    rcases hpair 0 with ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h0
    · rcases hpair 1 with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd (h0.symm.trans h1) (by decide)
      · exact absurd (h0.symm.trans h1) (by decide)
  have hcs : ∀ j : Fin 5, σ⁻¹ j.castSucc = j.castSucc := fun j => by
    rcases hpair j with ⟨-, hj⟩ | ⟨hj, -⟩
    · exact hj
    · exact absurd (h5.symm.trans hj) (Fin.castSucc_lt_last j).ne'
  refine inv_eq_one.mp (Equiv.ext fun k => ?_)
  induction k using Fin.lastCases with
  | last => exact h5
  | cast j => exact hcs j

theorem exists_sixHom :
    ∃ ρ : Equiv.Perm (Fin 6) →* GL (Fin 5) (ZMod 2),
      Function.Injective ρ ∧
      (∀ σ : Equiv.Perm (Fin 6), (ρ σ : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        (ρ σ : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = 1) ∧
      (∀ (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2), ∑ i, x i = 0 →
        sixToFive (sixPermVec σ x) = (ρ σ : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ sixToFive x) := by
  refine ⟨sixActionHom.toHomUnits, ?_, fun σ => sixActionMatrix_orth σ,
    fun σ x hx => sixActionMatrix_equivariant σ x hx⟩
  refine (injective_iff_map_eq_one _).2 fun σ hσ => ?_
  have h1 : sixActionMatrix σ = 1 :=
    congrArg (fun u : GL (Fin 5) (ZMod 2) => (u : Matrix (Fin 5) (Fin 5) (ZMod 2))) hσ
  refine eq_one_of_fixes_sixTestVec σ fun i => ?_
  rw [sixActionMatrix_equivariant σ (sixTestVec i) (sum_sixTestVec i), h1, Matrix.one_mulVec]

end CFSG.ASVolI.ChH
