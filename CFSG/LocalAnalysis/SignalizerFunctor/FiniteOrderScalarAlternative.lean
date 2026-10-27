module

public import CFSG.LocalAnalysis.SignalizerFunctor.CharacterIntegrality
public import CFSG.LocalAnalysis.SignalizerFunctor.RootOfUnityAverageRigidity
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

public section

universe vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem finite_order_operator_semisimple
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    (operator : Module.End ℂ VectorType) (order : ℕ) (order_positive : 0 < order)
    (finite_order : operator ^ order = 1) : operator.IsSemisimple := by
  have order_ne : (order : ℂ) ≠ 0 := by exact_mod_cast order_positive.ne'
  have squarefree := (Polynomial.separable_X_pow_sub_C (1 : ℂ) order_ne one_ne_zero).squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero squarefree
  simpa only [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, map_one, sub_self] using
    congrArg (fun candidate : Module.End ℂ VectorType => candidate - 1) finite_order

theorem semisimple_operator_eq_scalar_of_single_eigenvalue
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    [FiniteDimensional ℂ VectorType]
    (operator : Module.End ℂ VectorType) (semisimple : operator.IsSemisimple)
    (scalar : ℂ) (single : ∀ eigenvalue, operator.HasEigenvalue eigenvalue → eigenvalue = scalar) :
    operator = scalar • (1 : Module.End ℂ VectorType) := by
  have eigenspace_top : operator.eigenspace scalar = ⊤ := by
    apply top_unique
    rw [← semisimple.iSup_eigenspace_eq_top]
    apply iSup_le
    intro eigenvalue
    by_cases eigen : operator.HasEigenvalue eigenvalue
    · rw [single eigenvalue eigen]
    · have zero : operator.eigenspace eigenvalue = ⊥ := by
        simpa only [Module.End.hasEigenvalue_iff, not_not] using eigen
      rw [zero]
      exact bot_le
  ext vector
  have member : vector ∈ operator.eigenspace scalar := by rw [eigenspace_top]; trivial
  simpa only [LinearMap.smul_apply, Module.End.one_apply] using Module.End.mem_eigenspace_iff.mp member

theorem finite_order_integral_trace_ratio_scalar_alternative
    {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module ℂ VectorType]
    [FiniteDimensional ℂ VectorType] [Nontrivial VectorType]
    (operator : Module.End ℂ VectorType) (order : ℕ) (order_positive : 0 < order)
    (finite_order : operator ^ order = 1)
    (integral : IsIntegral ℤ ((LinearMap.trace ℂ VectorType) operator / (Module.finrank ℂ VectorType : ℂ))) :
    (LinearMap.trace ℂ VectorType) operator = 0 ∨
      operator = ((LinearMap.trace ℂ VectorType) operator / (Module.finrank ℂ VectorType : ℂ)) •
        (1 : Module.End ℂ VectorType) := by
  classical
  let eigenvalues := operator.charpoly.roots.toList
  have length_equal : eigenvalues.length = Module.finrank ℂ VectorType := by
    rw [Multiset.length_toList, ← (IsAlgClosed.splits operator.charpoly).natDegree_eq_card_roots,
      LinearMap.charpoly_natDegree]
  have length_positive : 0 < eigenvalues.length := by
    rw [length_equal]
    exact Module.finrank_pos (R := ℂ) (M := VectorType)
  let : Nonempty (Fin eigenvalues.length) := Fin.pos_iff_nonempty.mp length_positive
  let values : Fin eigenvalues.length → ℂ := eigenvalues.get
  have trace_sum : (LinearMap.trace ℂ VectorType) operator = ∑ index, values index := by
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    change operator.charpoly.roots.sum = ∑ index, eigenvalues.get index
    calc
      _ = eigenvalues.sum := (Multiset.sum_toList _).symm
      _ = (List.ofFn eigenvalues.get).sum := congrArg List.sum (List.ofFn_get eigenvalues).symm
      _ = _ := List.sum_ofFn
  have roots : ∀ index, ∃ exponent : ℕ, 0 < exponent ∧ values index ^ exponent = 1 := by
    intro index
    have member : values index ∈ operator.charpoly.roots :=
      Multiset.mem_toList.mp (List.get_mem eigenvalues index)
    have eigen := (Module.End.hasEigenvalue_iff_isRoot_charpoly operator (values index)).mpr
      (Polynomial.mem_roots'.mp member).2
    exact ⟨order, order_positive, finite_order_eigenvalue_pow_eq_one operator order finite_order (values index) eigen⟩
  have average_equal : (∑ index, values index) / (Fintype.card (Fin eigenvalues.length) : ℂ) =
      (LinearMap.trace ℂ VectorType) operator / (Module.finrank ℂ VectorType : ℂ) := by
    simpa only [Fintype.card_fin, length_equal] using
      congrArg (fun numerator : ℂ => numerator / (Module.finrank ℂ VectorType : ℂ)) trace_sum.symm
  have average_integral : IsIntegral ℤ ((∑ index, values index) / (Fintype.card (Fin eigenvalues.length) : ℂ)) := by
    rwa [average_equal]
  rcases integral_root_of_unity_average_rigidity values roots average_integral with zero | constant
  · left
    rw [average_equal] at zero
    have rank_ne : (Module.finrank ℂ VectorType : ℂ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := ℂ) (M := VectorType)).ne'
    exact (div_eq_zero_iff.mp zero).resolve_right rank_ne
  right
  apply semisimple_operator_eq_scalar_of_single_eigenvalue operator
    (finite_order_operator_semisimple operator order order_positive finite_order)
  intro eigenvalue eigen
  have root := (Module.End.hasEigenvalue_iff_isRoot_charpoly operator eigenvalue).mp eigen
  have member : eigenvalue ∈ eigenvalues := Multiset.mem_toList.mpr (Polynomial.mem_roots'.mpr ⟨operator.charpoly_monic.ne_zero, root⟩)
  obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
  rw [← equal]
  simpa only [average_equal] using constant index

end CFSG.SignalizerFunctor.Helpers
