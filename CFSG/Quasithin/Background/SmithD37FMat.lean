module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTensor

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.QuasithinUnique.Setup
open scoped Matrix TensorProduct

section Coord

variable {F : Type} [Field F] {V : Fin 2 → Type} [∀ i, AddCommGroup (V i)]
  [∀ i, Module F (V i)] {kk : Fin 2 → ℕ} (b : ∀ i, Module.Basis (Fin (kk i)) F (V i))

@[expose] noncomputable def coordML : MultilinearMap F V (Matrix (Fin (kk 0)) (Fin (kk 1)) F) where
  toFun m := Matrix.vecMulVec ((b 0).repr (m 0)) ((b 1).repr (m 1))
  map_update_add' m i x y := by
    fin_cases i
    · simp [Matrix.add_vecMulVec]
    · simp [Matrix.vecMulVec_add]
  map_update_smul' m i c x := by
    fin_cases i
    · simp [Matrix.smul_vecMulVec]
    · simp [Matrix.vecMulVec_smul]

@[expose] noncomputable def coordLin : (⨂[F] i, V i) →ₗ[F] Matrix (Fin (kk 0)) (Fin (kk 1)) F :=
  PiTensorProduct.lift (coordML b)

theorem coordLin_tprod (m : ∀ i, V i) :
    coordLin b (PiTensorProduct.tprod F m) =
      Matrix.vecMulVec ((b 0).repr (m 0)) ((b 1).repr (m 1)) :=
  PiTensorProduct.lift.tprod m

noncomputable abbrev matOf (i : Fin 2) (f : Module.End F (V i)) :
    Matrix (Fin (kk i)) (Fin (kk i)) F :=
  LinearMap.toMatrix (b i) (b i) f

theorem coordLin_factorEnd_zero (f : Module.End F (V 0)) (x : ⨂[F] i, V i) :
    coordLin b (Offender.factorEnd 0 f x) = matOf b 0 f * coordLin b x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, Offender.factorEnd_tprod, coordLin_tprod, coordLin_tprod,
      Matrix.mul_smul, Matrix.mul_vecMulVec, LinearMap.toMatrix_mulVec_repr]
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Matrix.mul_add]

theorem coordLin_factorEnd_one (g : Module.End F (V 1)) (x : ⨂[F] i, V i) :
    coordLin b (Offender.factorEnd 1 g x) = coordLin b x * (matOf b 1 g)ᵀ := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [map_smul, map_smul, map_smul, Offender.factorEnd_tprod, coordLin_tprod, coordLin_tprod,
      Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
      LinearMap.toMatrix_mulVec_repr]
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Matrix.add_mul]

theorem coordLin_apply (x : ⨂[F] i, V i) (a : Fin (kk 0)) (c : Fin (kk 1)) :
    coordLin b x a c = (Basis.piTensorProduct b).repr x
      ((piFinTwoEquiv fun i => Fin (kk i)).symm (a, c)) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [map_smul, coordLin_tprod, Matrix.smul_apply, Finsupp.smul_apply,
      Basis.piTensorProduct_repr_tprod_apply, Fin.prod_univ_two, Matrix.vecMulVec_apply]
    rfl
  | add x y hx hy =>
    simp only [map_add, Matrix.add_apply, Finsupp.add_apply, hx, hy]

theorem coordLin_bijective : Function.Bijective (coordLin b) := by
  set B := Basis.piTensorProduct b
  set E := piFinTwoEquiv fun i => Fin (kk i)
  constructor
  · intro x y hxy
    apply B.repr.injective
    ext p
    have h := congrFun (congrFun hxy (E p).1) (E p).2
    rw [coordLin_apply, coordLin_apply, Prod.mk.eta, Equiv.symm_apply_apply] at h
    exact h
  · intro X
    refine ⟨B.repr.symm (Finsupp.equivFunOnFinite.symm fun p => X (E p).1 (E p).2), ?_⟩
    ext a c
    rw [coordLin_apply, LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm]
    show X (E (E.symm (a, c))).1 (E (E.symm (a, c))).2 = X a c
    rw [Equiv.apply_symm_apply]

@[expose] noncomputable def coordEquiv :
    (⨂[F] i, V i) ≃ₗ[F] Matrix (Fin (kk 0)) (Fin (kk 1)) F :=
  LinearEquiv.ofBijective (coordLin b) (coordLin_bijective b)

end Coord

end CFSG.Quasithin.SmithD37
