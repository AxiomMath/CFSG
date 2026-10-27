module

public import CFSG.RankThree.PartTwo.Census.Spin.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.IntegralMatrix

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ) (hn : 4 ≤ n)

abbrev V : Type := ExteriorAlgebra ℚ (polarization n).W

@[expose] noncomputable def ρL : Matrix.ToLieAlgebra ℚ (CartanMatrix.D n) →ₗ⁅ℚ⁆
    Module.End ℚ (V n) :=
  (rep n hn).toLieHom.comp (UniversalEnvelopingAlgebra.ι ℚ)

theorem ρL_apply (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.D n)) :
    ρL n hn x = rep n hn (UniversalEnvelopingAlgebra.ι ℚ x) :=
  rfl

@[expose] noncomputable def E (i : Fin n) : Module.End ℚ (V n) :=
  ρL n hn (serreE ℚ (CartanMatrix.D n) i)

@[expose] noncomputable def F (i : Fin n) : Module.End ℚ (V n) :=
  ρL n hn (serreF ℚ (CartanMatrix.D n) i)

@[expose] noncomputable def H (i : Fin n) : Module.End ℚ (V n) :=
  ρL n hn (serreH ℚ (CartanMatrix.D n) i)

theorem serre : IsSerreSystem ℚ (CartanMatrix.D n) (H n hn) (E n hn) (F n hn) :=
  (isSerreSystem_serre ℚ (CartanMatrix.D n)).map (ρL n hn)

theorem E_eq (i : Fin n) :
    E n hn i = rep n hn (UniversalEnvelopingAlgebra.ι ℚ
      (serreRootGenerator (CartanMatrix.D n) (.inl i))) := by
  rw [E, ρL_apply, serreRootGenerator_inl]

theorem F_eq (i : Fin n) :
    F n hn i = rep n hn (UniversalEnvelopingAlgebra.ι ℚ
      (serreRootGenerator (CartanMatrix.D n) (.inr i))) := by
  rw [F, ρL_apply, serreRootGenerator_inr]

@[expose] noncomputable def wt (a : Fin (dimension n)) (i : Fin n) : ℤ := basisWeight n a i

theorem H_apply (i : Fin n) (a : Fin (dimension n)) :
    H n hn i (latticeBasis n a : V n) = ((wt n a i : ℤ) : ℚ) • (latticeBasis n a : V n) :=
  (UniversalEnvelopingAlgebra.isCartanWeightVector_iff _ _).1
    (isCartanWeightVector_latticeBasis n hn a) i

theorem exists_wt_eq_one (i : Fin n) : ∃ a : Fin (dimension n), wt n a i = 1 := by
  by_cases hi : (i : ℕ) + 1 < n
  · refine ⟨Fintype.equivFin (Finset (Fin n)) {i}, ?_⟩
    rw [wt, basisWeight, signSet, Equiv.symm_apply_apply, DynkinType.typeDSpinWeight_apply,
      dite_eq_left hi]
    have hne : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ≠ i := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [hne]
  · refine ⟨Fintype.equivFin (Finset (Fin n))
      {(⟨n - 2, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)}, ?_⟩
    rw [wt, basisWeight, signSet, Equiv.symm_apply_apply, DynkinType.typeDSpinWeight_apply,
      dite_eq_right hi]
    have hi' : (i : ℕ) = n - 1 := by omega
    have h1 : (⟨(i : ℕ) - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := by
      ext
      simp only
      omega
    have hmem : i ∈ ({(⟨n - 2, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)} : Finset (Fin n)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Fin.ext hi'))
    rw [h1, ite_eq_left hmem]
    simp

theorem intRootData : IntRootData (CartanMatrix.D n)
    (fun i => rootIntMatrix n hn (.inl i)) (fun i => rootIntMatrix n hn (.inr i)) (wt n) :=
  IntRootData.ofRat (latticeBasis n) (serre n hn) (fun i => CartanMatrix.D_diag n i)
    (fun i => by
      rw [E_eq, ← pow_two]
      exact (polarization n).typeDSpinRep_rootGenerator_sq (polarizationBasis n) hn _)
    (fun i => by
      rw [F_eq, ← pow_two]
      exact (polarization n).typeDSpinRep_rootGenerator_sq (polarizationBasis n) hn _)
    (fun i s => by rw [E_eq]; exact rep_rootGenerator_latticeBasis_eq_sum n hn (.inl i) s)
    (fun i s => by rw [F_eq]; exact rep_rootGenerator_latticeBasis_eq_sum n hn (.inr i) s)
    (fun a i => H_apply n hn i a) (exists_wt_eq_one n)

omit hn in
theorem D_symm (a b : Fin n) : CartanMatrix.D n a b = CartanMatrix.D n b a := by
  rw [← transpose_apply (CartanMatrix.D n) b a, CartanMatrix.D_transpose]

@[expose] noncomputable def rootData (K : Type) [Field K] :
    RootData K (Fin (dimension n)) (Fin n) :=
  RootData.ofInt (intRootData n hn) (points n hn K) (fun k => rootSubgroupPoints n hn k K)
    (weightTorusPoints n hn K)
    (fun i u => coe_rootSubgroupPoints_eq_one_add_smul n hn (.inl i) K u)
    (fun i u => coe_rootSubgroupPoints_eq_one_add_smul n hn (.inr i) K u)
    (fun s => by
      rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
      simp only [torusCharacter_def]
      rfl)
    (fun s i u => by
      rw [weightTorusPoints_conj_rootSubgroupPoints, torusCharacter_def]
      congr 4
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [TypeDStd.rootGeneratorWeight_inl, D_symm])
    (fun s i u => by
      rw [weightTorusPoints_conj_rootSubgroupPoints, torusCharacter_def]
      congr 4
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [TypeDStd.rootGeneratorWeight_inr, D_symm, _root_.zpow_neg])

theorem rootData_G (K : Type) [Field K] : (rootData n hn K).G = points n hn K := rfl

theorem rootData_root (K : Type) [Field K] (k : Fin n ⊕ Fin n) :
    (rootData n hn K).root k = rootSubgroupPoints n hn k K := rfl

theorem rootData_torus (K : Type) [Field K] :
    (rootData n hn K).torus = weightTorusPoints n hn K := rfl

theorem rootData_CM (K : Type) [Field K] : (rootData n hn K).CM = CartanMatrix.D n := rfl

end CFSG.RankThree.PartTwo.Census.Spin.CarrierD
