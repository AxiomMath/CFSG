module

public import CFSG.RankThree.PartTwo.Census.Spin.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SerreRelations

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierB

open TauCeti TauCeti.TypeBSpinCarrier Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

abbrev V : Type := ExteriorAlgebra ℚ (polarization n).W

@[expose] noncomputable def ρL : LieAlgebra.Orthogonal.typeB (Fin (n + 1)) ℚ →ₗ⁅ℚ⁆
    Module.End ℚ (V n) :=
  (rep n).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℚ)

theorem ρL_apply (x : LieAlgebra.Orthogonal.typeB (Fin (n + 1)) ℚ) :
    ρL n x = rep n (UniversalEnvelopingAlgebra.ι ℚ x) :=
  rfl

@[expose] noncomputable def E (i : Fin (n + 1)) : Module.End ℚ (V n) :=
  ρL n (typeBSimpleRootGenerator i)

@[expose] noncomputable def F (i : Fin (n + 1)) : Module.End ℚ (V n) :=
  ρL n (typeBSimpleNegativeRootGenerator i)

@[expose] noncomputable def H (i : Fin (n + 1)) : Module.End ℚ (V n) :=
  ρL n (typeBSimpleCorootGenerator i)

theorem serre : IsSerreSystem ℚ (CartanMatrix.B (n + 1)).transpose (H n) (E n) (F n) :=
  isSerreSystem_typeBSimpleRootGenerator.map (ρL n)

theorem E_eq (i : Fin (n + 1)) :
    E n i = rep n (UniversalEnvelopingAlgebra.ι ℚ (typeBSimpleRootGeneratorFamily (.inl i))) := by
  rw [E, ρL_apply, typeBSimpleRootGeneratorFamily_inl]

theorem F_eq (i : Fin (n + 1)) :
    F n i = rep n (UniversalEnvelopingAlgebra.ι ℚ (typeBSimpleRootGeneratorFamily (.inr i))) := by
  rw [F, ρL_apply, typeBSimpleRootGeneratorFamily_inr]

@[expose] noncomputable def wt (a : Fin (dimension n)) (i : Fin (n + 1)) : ℤ := basisWeight n a i

theorem H_apply (i : Fin (n + 1)) (a : Fin (dimension n)) :
    H n i (latticeBasis n a : V n) = ((wt n a i : ℤ) : ℚ) • (latticeBasis n a : V n) :=
  (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).1
    (isCartanWeightVector_latticeBasis n a) i

theorem exists_wt_eq_one (i : Fin (n + 1)) : ∃ a : Fin (dimension n), wt n a i = 1 := by
  refine ⟨Fintype.equivFin (Finset (Fin (n + 1))) {i}, ?_⟩
  rw [wt, basisWeight, signSet, Equiv.symm_apply_apply]
  by_cases hi : (i : ℕ) + 1 < n + 1
  · rw [DynkinType.typeBSpinWeight_eq_one_iff_of_lt hi]
    refine ⟨Finset.mem_singleton_self i, ?_⟩
    have hnotmax : ¬ IsMax i :=
      not_isMax_of_lt (b := (⟨(i : ℕ) + 1, hi⟩ : Fin (n + 1))) (by simp [Fin.lt_def])
    rw [Finset.mem_singleton, Order.succ_eq_iff_isMax]
    exact hnotmax
  · rw [DynkinType.typeBSpinWeight_eq_one_iff_of_last hi]
    exact Finset.mem_singleton_self i

theorem intRootData : IntRootData (CartanMatrix.B (n + 1)).transpose
    (fun i => rootIntMatrix n (.inl i)) (fun i => rootIntMatrix n (.inr i)) (wt n) :=
  IntRootData.ofRat (latticeBasis n) (serre n) (fun i => CartanMatrix.B_diag (n + 1) i)
    (fun i => by rw [E_eq, ← pow_two]; exact pow_two_rep_rootGenerator_eq_zero n _)
    (fun i => by rw [F_eq, ← pow_two]; exact pow_two_rep_rootGenerator_eq_zero n _)
    (fun i s => by rw [E_eq]; exact rep_rootGenerator_latticeBasis_eq_sum n (.inl i) s)
    (fun i s => by rw [F_eq]; exact rep_rootGenerator_latticeBasis_eq_sum n (.inr i) s)
    (fun a i => H_apply n i a) (exists_wt_eq_one n)

@[expose] noncomputable def rootData (K : Type) [Field K] :
    RootData K (Fin (dimension n)) (Fin (n + 1)) :=
  RootData.ofInt (intRootData n) (points n K) (fun k => rootSubgroupPoints n k K)
    (weightTorusPoints n K)
    (fun i u => coe_rootSubgroupPoints_eq_one_add_smul n (.inl i) K u)
    (fun i u => coe_rootSubgroupPoints_eq_one_add_smul n (.inr i) K u)
    (fun s => by
      rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
      simp only [torusCharacter_def]
      rfl)
    (fun s i u => by
      rw [weightTorusPoints_conj_rootSubgroupPoints, rootWeight_inl, torusCharacter_def]
      rfl)
    (fun s i u => by
      rw [weightTorusPoints_conj_rootSubgroupPoints, rootWeight_inr, torusCharacter_neg,
        torusCharacter_def]
      rfl)

theorem rootData_G (K : Type) [Field K] : (rootData n K).G = points n K := rfl

theorem rootData_root (K : Type) [Field K] (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (rootData n K).root k = rootSubgroupPoints n k K := rfl

theorem rootData_torus (K : Type) [Field K] : (rootData n K).torus = weightTorusPoints n K := rfl

theorem rootData_CM (K : Type) [Field K] :
    (rootData n K).CM = (CartanMatrix.B (n + 1)).transpose := rfl

end CFSG.RankThree.PartTwo.Census.Spin.CarrierB
