module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtendScalars
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.KrullSchmidt

namespace CFSG
end CFSG
open CFSG

/-!
# Scalar-descent infrastructure

Finite-dimensional linear-map spaces commute with extension of scalars.
-/

open scoped MonoidAlgebra
open scoped TensorProduct

noncomputable section

namespace LinearMap

private theorem baseChange_linearMap_basis
    {F E V W ι κ : Type*} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (bV : Module.Basis ι F V) (bW : Module.Basis κ F W) (ij : κ × ι) :
    baseChange E (bV.linearMap bW ij) =
      (bV.baseChange E).linearMap (bW.baseChange E) ij := by
  apply Module.Basis.ext (bV.baseChange E)
  intro i
  rw [Module.Basis.linearMap_apply_apply]
  rw [Module.Basis.baseChange_apply, baseChange_tmul,
    Module.Basis.linearMap_apply_apply]
  split <;> simp_all [Module.Basis.baseChange_apply]

/-- The canonical scalar-extension equivalence between finite-dimensional
linear-map spaces. -/
@[expose]
public noncomputable def baseChangeLinearMapEquiv
    (F E V W : Type*) [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] :
    E ⊗[F] (V →ₗ[F] W) ≃ₗ[E] (E ⊗[F] V →ₗ[E] E ⊗[F] W) := by
  classical
  let bV := Module.Basis.ofVectorSpace F V
  let bW := Module.Basis.ofVectorSpace F W
  exact ((bV.linearMap bW).baseChange E).equiv
    ((bV.baseChange E).linearMap (bW.baseChange E)) (Equiv.refl _)

set_option maxRecDepth 2000 in
/-- On pure tensors, baseChangeLinearMapEquiv is the usual base-changed
linear map. -/
public theorem baseChangeLinearMapEquiv_tmul
    (F E V W : Type*) [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (a : E) (f : V →ₗ[F] W) :
    baseChangeLinearMapEquiv F E V W (a ⊗ₜ[F] f) =
      a • baseChange E f := by
  classical
  let bV := Module.Basis.ofVectorSpace F V
  let bW := Module.Basis.ofVectorSpace F W
  let bHom := bV.linearMap bW
  let e := baseChangeLinearMapEquiv F E V W
  let L : (V →ₗ[F] W) →ₗ[F] (E ⊗[F] V →ₗ[E] E ⊗[F] W) :=
    (e.toLinearMap.restrictScalars F).comp
      ((TensorProduct.mk F E (V →ₗ[F] W)) a)
  let R : (V →ₗ[F] W) →ₗ[F] (E ⊗[F] V →ₗ[E] E ⊗[F] W) :=
    (((LinearMap.lsmul E (E ⊗[F] V →ₗ[E] E ⊗[F] W)) a).restrictScalars F).comp
      (baseChangeHom F E V W)
  change L f = R f
  apply DFunLike.congr_fun (Module.Basis.ext bHom ?_) f
  intro ij
  change e (a ⊗ₜ[F] bHom ij) = a • baseChange E (bHom ij)
  have ht : a • (1 ⊗ₜ[F] bHom ij) = a ⊗ₜ[F] bHom ij := by
    simpa using (TensorProduct.smul_tmul' (R := F) a (1 : E) (bHom ij))
  rw [← ht, e.map_smul]
  congr 1
  have he_basis :
      e ((bHom.baseChange E) ij) =
        (bV.baseChange E).linearMap (bW.baseChange E) ij := by
    simpa [e, baseChangeLinearMapEquiv, bHom, bV, bW] using
      (Module.Basis.equiv_apply
        (bHom.baseChange E) ij
        ((bV.baseChange E).linearMap (bW.baseChange E))
        (Equiv.refl _))
  calc
    e (1 ⊗ₜ[F] bHom ij) = e ((bHom.baseChange E) ij) := by
      rw [Module.Basis.baseChange_apply]
    _ = (bV.baseChange E).linearMap (bW.baseChange E) ij := he_basis
    _ = baseChange E (bHom ij) :=
      (baseChange_linearMap_basis bV bW ij).symm

/-- Flat scalar extension commutes with kernels of linear maps. -/
public theorem baseChange_ker_eq
    {F E V W : Type*} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (T : V →ₗ[F] W) :
    T.ker.baseChange E = (T.baseChange E).ker := by
  have hex := Module.Flat.lTensor_exact (M := E) (LinearMap.exact_subtype_ker_map T)
  ext y
  change y ∈ LinearMap.range (T.ker.subtype.baseChange E) ↔
    y ∈ LinearMap.ker (T.baseChange E)
  change y ∈ LinearMap.range (LinearMap.lTensor E T.ker.subtype) ↔
    y ∈ LinearMap.ker (LinearMap.lTensor E T)
  simpa [LinearMap.mem_range, LinearMap.mem_ker] using (hex y).symm

/-- The base change of a kernel is canonically equivalent to the kernel of
the base-changed map. -/
@[expose]
public noncomputable def kerBaseChangeEquiv
    {F E V W : Type*} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (T : V →ₗ[F] W) :
    E ⊗[F] T.ker ≃ₗ[E] (T.baseChange E).ker := by
  let f := Submodule.toBaseChange E T.ker
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hcoe := congrArg Subtype.val hxy
    change T.ker.subtype.baseChange E x = T.ker.subtype.baseChange E y at hcoe
    have hsub : Function.Injective T.ker.subtype := fun u v huv => Subtype.ext huv
    apply Module.Flat.lTensor_preserves_injective_linearMap T.ker.subtype hsub
    simpa only [LinearMap.baseChange_eq_ltensor] using hcoe
  let e0 : E ⊗[F] T.ker ≃ₗ[E] T.ker.baseChange E :=
    LinearEquiv.ofBijective f ⟨hf_inj, Submodule.toBaseChange_surjective E T.ker⟩
  exact e0.trans (LinearEquiv.ofEq _ _ (baseChange_ker_eq T))
end LinearMap

namespace CFSG.Theory.Representation

open _root_.Representation

variable {F E G V W : Type*} [Field F] [Field E] [Algebra F E] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

public def intertwiningConstraint (rho : Representation F G V) (sigma : Representation F G W)
    (g : G) : (V →ₗ[F] W) →ₗ[F] (V →ₗ[F] W) :=
  { toFun := fun f => f.comp (rho g) - (sigma g).comp f
    map_add' := by intro f h; ext x; simp; abel
    map_smul' := by intro a f; ext x; simp [smul_sub] }

public def intertwiningConstraintSpan (rho : Representation F G V)
    (sigma : Representation F G W) :
    Submodule F ((V →ₗ[F] W) →ₗ[F] (V →ₗ[F] W)) :=
  Submodule.span F (Set.range (intertwiningConstraint rho sigma))

public def finiteIntertwiningConstraint (rho : Representation F G V)
    (sigma : Representation F G W) :
    (V →ₗ[F] W) →ₗ[F]
      (Fin (Module.finrank F (intertwiningConstraintSpan rho sigma)) → (V →ₗ[F] W)) := by
  letI : Module.Free F (intertwiningConstraintSpan rho sigma) :=
    Module.Free.of_divisionRing F (intertwiningConstraintSpan rho sigma)
  exact LinearMap.pi fun i =>
    (Module.finBasis F (intertwiningConstraintSpan rho sigma) i).val

public theorem mem_ker_finiteIntertwiningConstraint_iff
    (rho : Representation F G V) (sigma : Representation F G W)
    (f : V →ₗ[F] W) :
    f ∈ (finiteIntertwiningConstraint rho sigma).ker ↔
      ∀ g : G, f.comp (rho g) = (sigma g).comp f := by
  let : Module.Free F (intertwiningConstraintSpan rho sigma) :=
    Module.Free.of_divisionRing F (intertwiningConstraintSpan rho sigma)
  rw [LinearMap.mem_ker]
  constructor
  · intro hf g
    apply sub_eq_zero.mp
    let C := intertwiningConstraintSpan rho sigma
    let b := Module.finBasis F C
    let c : C := ⟨intertwiningConstraint rho sigma g,
      Submodule.subset_span (Set.mem_range_self g)⟩
    let ev : C →ₗ[F] (V →ₗ[F] W) :=
      { toFun := fun z => z.val f
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    have hbi (i) : (b i).val f = 0 := by
      have hi := congrFun hf i
      exact hi
    calc
      (intertwiningConstraint rho sigma g) f = c.val f := rfl
      _ = (∑ i, (b.repr c i) • (b i : C)).val f :=
        congrArg (fun z : C => z.val f) (b.sum_repr c).symm
      _ = ∑ i, (b.repr c i) • (b i).val f := by
        change ev (∑ i, (b.repr c i) • (b i : C)) = _
        rw [map_sum]
        simp [ev]
      _ = 0 := by simp [hbi]
  · intro hf
    funext i
    change (Module.finBasis F (intertwiningConstraintSpan rho sigma) i).val f = 0
    refine Submodule.span_induction
      (p := fun c _ => c f = 0)
      ?_ ?_ ?_ ?_
      (Module.finBasis F (intertwiningConstraintSpan rho sigma) i).property
    · rintro _ ⟨g, rfl⟩
      exact sub_eq_zero.mpr (hf g)
    · rfl
    · intro x y hx hy hxf hyf
      simp [hxf, hyf]
    · intro a x hx hxf
      simp [hxf]

public def kerFiniteIntertwiningConstraintEquiv
    (rho : Representation F G V) (sigma : Representation F G W) :
    (finiteIntertwiningConstraint rho sigma).ker ≃ₗ[F] (rho →ₗ sigma) where
  toFun f := RepMap.mk f.1 ((mem_ker_finiteIntertwiningConstraint_iff rho sigma f.1).mp f.2)
  invFun f := ⟨f.toLinearMap, (mem_ker_finiteIntertwiningConstraint_iff rho sigma f.toLinearMap).mpr f.isIntertwining'⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

public def baseChangedEnd (c : (V →ₗ[F] W) →ₗ[F] (V →ₗ[F] W)) :
    (E ⊗[F] V →ₗ[E] E ⊗[F] W) →ₗ[E] (E ⊗[F] V →ₗ[E] E ⊗[F] W) :=
  let e := LinearMap.baseChangeLinearMapEquiv F E V W
  e.toLinearMap.comp ((c.baseChange E).comp e.symm.toLinearMap)

public theorem baseChangedEnd_intertwiningConstraint
    (rho : Representation F G V) (sigma : Representation F G W) (g : G) :
    baseChangedEnd (E := E) (intertwiningConstraint rho sigma g) =
      intertwiningConstraint (extendScalars E rho) (extendScalars E sigma) g := by
  let e := LinearMap.baseChangeLinearMapEquiv F E V W
  apply LinearMap.ext
  intro f
  obtain ⟨t, rfl⟩ := e.surjective f
  induction t using TensorProduct.induction_on with
  | zero =>
      simp [baseChangedEnd, intertwiningConstraint, e, sub_eq_add_neg]
      abel
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]
  | tmul a h =>
      have heh : e.symm (LinearMap.baseChange E h) = (1 : E) ⊗ₜ[F] h := by
        apply e.injective
        simp [e, LinearMap.baseChangeLinearMapEquiv_tmul]
      simp [baseChangedEnd, intertwiningConstraint, e,
        LinearMap.baseChangeLinearMapEquiv_tmul, LinearMap.baseChange_tmul,
        LinearMap.baseChange_sub, LinearMap.baseChange_comp, extendScalars_apply, heh]

set_option maxRecDepth 10000 in
@[expose]
public def baseChangedEndHom :
    ((V →ₗ[F] W) →ₗ[F] (V →ₗ[F] W)) →ₗ[F]
      ((E ⊗[F] V →ₗ[E] E ⊗[F] W) →ₗ[E] (E ⊗[F] V →ₗ[E] E ⊗[F] W)) where
  toFun := baseChangedEnd (E := E)
  map_add' c d := by
    apply LinearMap.ext
    intro f
    simp [baseChangedEnd]
  map_smul' a c := by
    let e := LinearMap.baseChangeLinearMapEquiv F E V W
    apply LinearMap.ext
    intro f
    change e (((a • c).baseChange E) (e.symm f)) =
      a • e ((c.baseChange E) (e.symm f))
    rw [LinearMap.baseChange_smul]
    exact e.toLinearMap.map_smul_of_tower a _

@[simp]
public theorem baseChangedEndHom_apply
    (c : (V →ₗ[F] W) →ₗ[F] (V →ₗ[F] W)) :
    baseChangedEndHom (F := F) (E := E) (V := V) (W := W) c =
      baseChangedEnd (E := E) c := rfl

public def baseChangedFiniteIntertwiningConstraint
    (rho : Representation F G V) (sigma : Representation F G W) :
    (E ⊗[F] V →ₗ[E] E ⊗[F] W) →ₗ[E]
      (Fin (Module.finrank F (intertwiningConstraintSpan rho sigma)) →
        (E ⊗[F] V →ₗ[E] E ⊗[F] W)) := by
  letI : Module.Free F (intertwiningConstraintSpan rho sigma) :=
    Module.Free.of_divisionRing F (intertwiningConstraintSpan rho sigma)
  exact LinearMap.pi fun i =>
    baseChangedEnd (E := E)
      (Module.finBasis F (intertwiningConstraintSpan rho sigma) i).val

public theorem mem_ker_baseChangedFiniteIntertwiningConstraint_iff
    (rho : Representation F G V) (sigma : Representation F G W)
    (f : E ⊗[F] V →ₗ[E] E ⊗[F] W) :
    f ∈ (baseChangedFiniteIntertwiningConstraint (E := E) rho sigma).ker ↔
      ∀ g : G, f.comp ((extendScalars E rho) g) =
        ((extendScalars E sigma) g).comp f := by
  let : Module.Free F (intertwiningConstraintSpan rho sigma) :=
    Module.Free.of_divisionRing F (intertwiningConstraintSpan rho sigma)
  rw [LinearMap.mem_ker]
  constructor
  · intro hf g
    apply sub_eq_zero.mp
    let C := intertwiningConstraintSpan rho sigma
    let b := Module.finBasis F C
    let c : C := ⟨intertwiningConstraint rho sigma g,
      Submodule.subset_span (Set.mem_range_self g)⟩
    let ev0 := baseChangedEndHom (F := F) (E := E) (V := V) (W := W)
    let ev : C →ₗ[F] (E ⊗[F] V →ₗ[E] E ⊗[F] W) :=
      { toFun := fun z => ev0 z.val f
        map_add' := by
          intro x y
          change ev0 (x.val + y.val) f = ev0 x.val f + ev0 y.val f
          rw [map_add, LinearMap.add_apply]
        map_smul' := by
          intro a x
          change ev0 (a • x.val) f = a • ev0 x.val f
          rw [map_smul, LinearMap.smul_apply] }
    have hbi (i) : baseChangedEnd (E := E) (b i).val f = 0 := by
      have hi := congrFun hf i
      exact hi
    calc
      (intertwiningConstraint (extendScalars E rho) (extendScalars E sigma) g) f =
          baseChangedEnd (E := E) (intertwiningConstraint rho sigma g) f := by
            rw [baseChangedEnd_intertwiningConstraint]
      _ = ev c := rfl
      _ = ev (∑ i, (b.repr c i) • (b i : C)) :=
        congrArg ev (b.sum_repr c).symm
      _ = ∑ i, (b.repr c i) • baseChangedEnd (E := E) (b i).val f := by
        rw [map_sum]
        simp [ev, ev0]
      _ = 0 := by simp [hbi]
  · intro hf
    funext i
    change baseChangedEnd (E := E)
      (Module.finBasis F (intertwiningConstraintSpan rho sigma) i).val f = 0
    refine Submodule.span_induction
      (p := fun c _ => baseChangedEnd (E := E) c f = 0)
      ?_ ?_ ?_ ?_
      (Module.finBasis F (intertwiningConstraintSpan rho sigma) i).property
    · rintro _ ⟨g, rfl⟩
      rw [baseChangedEnd_intertwiningConstraint]
      exact sub_eq_zero.mpr (hf g)
    · simp [baseChangedEnd]
    · intro x y hx hy hxf hyf
      change (baseChangedEndHom (F := F) (E := E) (V := V) (W := W) (x + y)) f = 0
      rw [map_add]
      change baseChangedEnd (E := E) x f + baseChangedEnd (E := E) y f = 0
      rw [hxf, hyf, zero_add]
    · intro a x hx hxf
      change (baseChangedEndHom (F := F) (E := E) (V := V) (W := W) (a • x)) f = 0
      rw [map_smul]
      change a • baseChangedEnd (E := E) x f = 0
      rw [hxf, smul_zero]

/-- Transporting a base-field endomorphism of `Hom` commutes with applying it
and then extending scalars. -/
@[simp]
public theorem baseChangedEnd_baseChange
    (c : (V →ₗ[F] W) →ₗ[F] (V →ₗ[F] W)) (f : V →ₗ[F] W) :
    baseChangedEnd (E := E) c (LinearMap.baseChange E f) =
      LinearMap.baseChange E (c f) := by
  let e := LinearMap.baseChangeLinearMapEquiv F E V W
  have hf : e.symm (LinearMap.baseChange E f) = (1 : E) ⊗ₜ[F] f := by
    apply e.injective
    simp [e, LinearMap.baseChangeLinearMapEquiv_tmul]
  simp [baseChangedEnd, e, hf, LinearMap.baseChangeLinearMapEquiv_tmul]

/-- The scalar extension of the finite product codomain, with each coordinate
identified with the extended linear-map space. -/
public noncomputable def finiteIntertwiningConstraintCodomainEquiv
    (rho : Representation F G V) (sigma : Representation F G W) :
    E ⊗[F] (Fin (Module.finrank F (intertwiningConstraintSpan rho sigma)) →
      (V →ₗ[F] W)) ≃ₗ[E]
      (Fin (Module.finrank F (intertwiningConstraintSpan rho sigma)) →
        (E ⊗[F] V →ₗ[E] E ⊗[F] W)) :=
  (TensorProduct.piRight F E E
    (fun _ : Fin (Module.finrank F (intertwiningConstraintSpan rho sigma)) =>
      (V →ₗ[F] W))).trans
    (LinearEquiv.piCongrRight fun _ =>
      LinearMap.baseChangeLinearMapEquiv F E V W)

/-- The base change of the finite intertwining constraint is conjugate to the
finite constraint on the extended linear-map space. -/
public theorem finiteIntertwiningConstraint_baseChange
    (rho : Representation F G V) (sigma : Representation F G W) :
    (finiteIntertwiningConstraintCodomainEquiv (E := E) rho sigma).toLinearMap.comp
        ((finiteIntertwiningConstraint rho sigma).baseChange E) =
      (baseChangedFiniteIntertwiningConstraint (E := E) rho sigma).comp
        (LinearMap.baseChangeLinearMapEquiv F E V W).toLinearMap := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]
  | tmul a f =>
      ext i
      simp [finiteIntertwiningConstraintCodomainEquiv,
        finiteIntertwiningConstraint, baseChangedFiniteIntertwiningConstraint,
        LinearMap.baseChangeLinearMapEquiv_tmul]

set_option maxRecDepth 10000 in
/-- Scalar extension of the base-field finite-constraint kernel is canonically
equivalent to the finite-constraint kernel on the extended Hom space. -/
public noncomputable def kerBaseChangedFiniteConstraintEquiv
    (rho : Representation F G V) (sigma : Representation F G W) :
    E ⊗[F] (finiteIntertwiningConstraint rho sigma).ker ≃ₗ[E]
      (baseChangedFiniteIntertwiningConstraint (E := E) rho sigma).ker := by
  let T := finiteIntertwiningConstraint rho sigma
  let e := LinearMap.baseChangeLinearMapEquiv F E V W
  let q := finiteIntertwiningConstraintCodomainEquiv (E := E) rho sigma
  let C := baseChangedFiniteIntertwiningConstraint (E := E) rho sigma
  have hcomm : q.toLinearMap.comp (T.baseChange E) = C.comp e.toLinearMap :=
    finiteIntertwiningConstraint_baseChange (E := E) rho sigma
  let k : (T.baseChange E).ker ≃ₗ[E] C.ker :=
    { toFun := fun x => ⟨e x, by
        rw [LinearMap.mem_ker]
        have hx := LinearMap.congr_fun hcomm x
        simpa [LinearMap.mem_ker.mp x.property] using hx.symm⟩
      invFun := fun y => ⟨e.symm y, by
        rw [LinearMap.mem_ker]
        apply q.injective
        have hy := LinearMap.congr_fun hcomm (e.symm y)
        simpa [LinearMap.mem_ker.mp y.property] using hy⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact e.map_add _ _
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact e.map_smul _ _
      left_inv := by intro x; exact Subtype.ext (e.symm_apply_apply x)
      right_inv := by intro y; exact Subtype.ext (e.apply_symm_apply y) }
  exact (LinearMap.kerBaseChangeEquiv T).trans k

/-- The transported finite-constraint kernel is the intertwining-map space of
the scalar-extended representations. -/
public def kerBaseChangedFiniteIntertwiningMapEquiv
    (rho : Representation F G V) (sigma : Representation F G W) :
    (baseChangedFiniteIntertwiningConstraint (E := E) rho sigma).ker ≃ₗ[E]
      (extendScalars E rho →ₗ extendScalars E sigma) where
  toFun f := RepMap.mk f.1
    ((mem_ker_baseChangedFiniteIntertwiningConstraint_iff rho sigma f.1).mp f.2)
  invFun f := ⟨f.toLinearMap,
    (mem_ker_baseChangedFiniteIntertwiningConstraint_iff rho sigma f.toLinearMap).mpr
      f.isIntertwining'⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxRecDepth 10000 in
/-- Scalar extension commutes with the finite-dimensional space of
intertwining maps. -/
public noncomputable def intertwiningMapBaseChangeEquiv
    (rho : Representation F G V) (sigma : Representation F G W) :
    E ⊗[F] (rho →ₗ sigma) ≃ₗ[E]
      (extendScalars E rho →ₗ extendScalars E sigma) :=
  ((kerFiniteIntertwiningConstraintEquiv rho sigma).symm.baseChange F E _ _).trans
    ((kerBaseChangedFiniteConstraintEquiv (E := E) rho sigma).trans
      (kerBaseChangedFiniteIntertwiningMapEquiv (E := E) rho sigma))

set_option maxRecDepth 20000 in
/-- On pure tensors, the intertwining-map base-change equivalence is the usual
scalar extension of an intertwiner. -/
@[simp]
public theorem intertwiningMapBaseChangeEquiv_tmul
    (rho : Representation F G V) (sigma : Representation F G W)
    (a : E) (f : rho →ₗ sigma) :
    intertwiningMapBaseChangeEquiv (E := E) rho sigma (a ⊗ₜ[F] f) =
      a • extendScalars_map E f := by
  apply RepMap.toLinearMap_injective
  change LinearMap.baseChangeLinearMapEquiv F E V W (a ⊗ₜ[F] f.toLinearMap) =
    a • LinearMap.baseChange E f.toLinearMap
  exact LinearMap.baseChangeLinearMapEquiv_tmul F E V W a f.toLinearMap


section DeterminantSpecialization

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The determinant of the generic linear combination of a finite basis of
intertwining maps. -/
public noncomputable def intertwinerDeterminantPolynomial
    (rho : Representation F G V) (sigma : Representation F G W)
    (bV : Module.Basis ι F V) (bW : Module.Basis ι F W)
    (b : Module.Basis κ F (rho →ₗ sigma)) : MvPolynomial κ F :=
  Matrix.det fun i j => ∑ k,
    MvPolynomial.C ((LinearMap.toMatrix bV bW) (b k).toLinearMap i j) *
      MvPolynomial.X k

omit [FiniteDimensional F V] [FiniteDimensional F W] [DecidableEq κ] in
/-- Evaluating the generic determinant after scalar extension gives the
matrix determinant of the corresponding linear combination of base-changed
intertwiners. -/
public theorem aeval_intertwinerDeterminantPolynomial
    {S : Type*} [Field S] [Algebra F S]
    (rho : Representation F G V) (sigma : Representation F G W)
    (bV : Module.Basis ι F V) (bW : Module.Basis ι F W)
    (b : Module.Basis κ F (rho →ₗ sigma)) (x : κ → S) :
    MvPolynomial.aeval x (intertwinerDeterminantPolynomial rho sigma bV bW b) =
      Matrix.det (LinearMap.toMatrix (bV.baseChange S) (bW.baseChange S)
        (∑ k, x k • LinearMap.baseChange S (b k).toLinearMap)) := by
  unfold intertwinerDeterminantPolynomial
  calc
    _ = Matrix.det ((MvPolynomial.aeval x).mapMatrix
        (fun i j => ∑ k,
          MvPolynomial.C ((LinearMap.toMatrix bV bW) (b k).toLinearMap i j) *
            MvPolynomial.X k)) := (MvPolynomial.aeval x).map_det _
    _ = Matrix.det (LinearMap.toMatrix (bV.baseChange S) (bW.baseChange S)
        (∑ k, x k • LinearMap.baseChange S (b k).toLinearMap)) := by
      congr 1
      ext i j
      change (MvPolynomial.aeval x)
          (∑ k, MvPolynomial.C ((LinearMap.toMatrix bV bW) (b k).toLinearMap i j) *
            MvPolynomial.X k) = _
      simp [LinearMap.toMatrix_apply, Algebra.smul_def, mul_comm]


omit [Fintype κ] [DecidableEq κ] in
/-- A nonzero multivariate polynomial over a field has a nonzero evaluation in
an algebraic closure. -/
public theorem exists_aeval_ne_zero_algebraicClosure
    (p : MvPolynomial κ F) (hp : p ≠ 0) :
    ∃ x : κ → AlgebraicClosure F, MvPolynomial.aeval x p ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.map_injective (algebraMap F (AlgebraicClosure F))
    (FaithfulSMul.algebraMap_injective F (AlgebraicClosure F))
  apply MvPolynomial.funext
  intro x
  simpa [MvPolynomial.aeval_def] using h x

omit [FiniteDimensional F V] [FiniteDimensional F W] [DecidableEq κ] in
/-- A specialization of the generic intertwiner determinant to a nonzero
value yields an equivalence of the scalar-extended representations. -/
public theorem repEquiv_of_aeval_intertwinerDeterminantPolynomial_ne_zero
    {S : Type*} [Field S] [Algebra F S]
    (rho : Representation F G V) (sigma : Representation F G W)
    (bV : Module.Basis ι F V) (bW : Module.Basis ι F W)
    (b : Module.Basis κ F (rho →ₗ sigma)) (x : κ → S)
    (hx : MvPolynomial.aeval x
      (intertwinerDeterminantPolynomial rho sigma bV bW b) ≠ 0) :
    Nonempty (extendScalars S rho ≃ₗ extendScalars S sigma) := by
  let f : extendScalars S rho →ₗ extendScalars S sigma :=
    ∑ k, x k • extendScalars_map S (b k)
  have hdet :
      Matrix.det (LinearMap.toMatrix (bV.baseChange S) (bW.baseChange S)
        f.toLinearMap) ≠ 0 := by
    have hmap :
        f.toLinearMap =
          ∑ k, x k • LinearMap.baseChange S (b k).toLinearMap := by
      change IntertwiningMap.toLinearMapl
        (ρ := extendScalars S rho) (σ := extendScalars S sigma)
        (∑ k, x k • extendScalars_map S (b k)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      change x k • (extendScalars_map S (b k)).toLinearMap = _
      rw [extendScalars_map_toLinearMap]
    rw [hmap]
    simpa only [aeval_intertwinerDeterminantPolynomial] using hx
  let e : (S ⊗[F] V) ≃ₗ[S] (S ⊗[F] W) :=
    LinearEquiv.ofIsUnitDet (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨RepEquiv.mk e ?_⟩
  intro g
  rw [show e.toLinearMap = f.toLinearMap by
    exact LinearEquiv.coe_ofIsUnitDet (isUnit_iff_ne_zero.mpr hdet)]
  exact f.isIntertwining' g

/-- An equivalence of group-algebra modules induces an equivalence of the
corresponding representations. -/
public def repEquivOfModuleEquiv
    (rho : Representation F G V) (sigma : Representation F G W)
    (e : rho.asModule ≃ₗ[MonoidAlgebra F G] sigma.asModule) :
    rho ≃ₗ sigma where
  toLinearEquiv :=
    rho.asModuleEquiv.symm |>.trans
      ((e.restrictScalars F).trans sigma.asModuleEquiv)
  isIntertwining' g := by
    ext v
    change sigma.asModuleEquiv
        (e (rho.asModuleEquiv.symm (rho g v))) =
      sigma g
        (sigma.asModuleEquiv (e (rho.asModuleEquiv.symm v)))
    rw [Representation.asModuleEquiv_symm_map_rho]
    rw [map_smul]
    simp only [Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]

/-- Restricting a finite scalar extension to the base field identifies the
base-changed vector space with finitely many copies of the original one. -/
public noncomputable def baseChangeEquivFinCopies
    {S X : Type*} [Field S] [Algebra F S]
    [AddCommGroup X] [Module F X] [FiniteDimensional F S] :
    S ⊗[F] X ≃ₗ[F] (Fin (Module.finrank F S) → X) :=
  (TensorProduct.equivFinsuppOfBasisLeft (Module.finBasis F S)).trans
    (Finsupp.linearEquivFunOnFinite F X (Fin (Module.finrank F S)))

omit [FiniteDimensional F V] in
/-- Finite-copy coordinates intertwine the base-changed action with the
coordinatewise original action. -/
public theorem baseChangeEquivFinCopies_map_extendScalars
    {S : Type*} [Field S] [Algebra F S] [FiniteDimensional F S]
    (rho : Representation F G V) (g : G) (z : S ⊗[F] V) :
    baseChangeEquivFinCopies (F := F) ((extendScalars S rho g) z) =
      fun i => rho g (baseChangeEquivFinCopies (F := F) z i) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      ext i
      simp
  | add x y hx hy =>
      ext i
      simp only [Pi.add_apply, map_add]
      rw [congrFun hx i, congrFun hy i]
  | tmul s v =>
      ext i
      simp [baseChangeEquivFinCopies, extendScalars_apply,
        LinearMap.baseChange_tmul]

/-- Noether-Deuring descent over a finite field extension, obtained by
restricting scalars and cancelling a nonzero finite number of copies. -/
public theorem repEquiv_of_finite_extension
    {S : Type*} [Field S] [Algebra F S] [FiniteDimensional F S]
    (rho : Representation F G V) (sigma : Representation F G W)
    (hS : Nonempty (extendScalars S rho ≃ₗ extendScalars S sigma)) :
    Nonempty (rho ≃ₗ sigma) := by
  classical
  let : Module (MonoidAlgebra F G) V :=
    Representation.instModuleMonoidAlgebraAsModule rho
  let : Module (MonoidAlgebra F G) W :=
    Representation.instModuleMonoidAlgebraAsModule sigma
  let : IsScalarTower F (MonoidAlgebra F G) V :=
    Representation.instIsScalarTowerMonoidAlgebraAsModule (ρ := rho)
  let : IsScalarTower F (MonoidAlgebra F G) W :=
    Representation.instIsScalarTowerMonoidAlgebraAsModule (ρ := sigma)
  let n := Module.finrank F S
  let qV : S ⊗[F] V ≃ₗ[F] (Fin n → V) :=
    baseChangeEquivFinCopies (F := F)
  let qW : S ⊗[F] W ≃ₗ[F] (Fin n → W) :=
    baseChangeEquivFinCopies (F := F)
  let eS := Classical.choice hS
  let eF : (Fin n → V) ≃ₗ[F] (Fin n → W) :=
    qV.symm.trans ((eS.toLinearEquiv.restrictScalars F).trans qW)
  have heF (g : G) (v : Fin n → V) :
      eF (fun i => rho g (v i)) = fun i => sigma g (eF v i) := by
    have hqV :
        qV.symm (fun i => rho g (v i)) =
          (extendScalars S rho g) (qV.symm v) := by
      apply qV.injective
      rw [qV.apply_symm_apply]
      rw [baseChangeEquivFinCopies_map_extendScalars]
      simp only [qV, n, baseChangeEquivFinCopies,
        LinearEquiv.apply_symm_apply]
    change qW (eS (qV.symm (fun i => rho g (v i)))) =
      fun i => sigma g (qW (eS (qV.symm v)) i)
    rw [hqV, eS.isIntertwining]
    exact baseChangeEquivFinCopies_map_extendScalars sigma g _
  let eR : (Fin n → V) ≃ₗ[MonoidAlgebra F G]
      (Fin n → W) :=
    { toEquiv := eF.toEquiv
      map_add' := eF.map_add
      map_smul' := by
        intro r v
        induction r using MonoidAlgebra.induction_linear with
        | zero =>
            exact eF.map_zero
        | add x y hx hy =>
            calc
              eF ((x + y) • v) = eF (x • v + y • v) := congrArg eF (add_smul x y v)
              eF (x • v + y • v) = eF (x • v) + eF (y • v) := eF.map_add _ _
              _ = x • eF v + y • eF v := congrArg₂ (· + ·) hx hy
              _ = (x + y) • eF v := (add_smul x y _).symm
        | single g a =>
            ext i
            change eF (fun j => rho.asAlgebraHom
              (MonoidAlgebra.single g a) (v j)) i =
              sigma.asAlgebraHom (MonoidAlgebra.single g a) (eF v i)
            rw [Representation.asAlgebraHom_single,
              Representation.asAlgebraHom_single]
            change eF (fun j => a • rho g (v j)) i =
              a • sigma g (eF v i)
            rw [show (fun j => a • rho g (v j)) =
              a • (fun j => rho g (v j)) by rfl, eF.map_smul]
            simp only [Pi.smul_apply]
            rw [congrFun (heF g v) i] }
  have hn : n ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨e⟩ :=
    Module.linearEquiv_of_fin_copies_linearEquiv
      (F := F) (R := MonoidAlgebra F G)
      (M := V) (N := W) n hn eR
  exact ⟨repEquivOfModuleEquiv rho sigma e⟩

omit [DecidableEq κ] in
/-- A nonzero generic intertwiner determinant gives an equivalence over a
finite algebraic extension, hence over the base field. -/
public theorem repEquiv_of_intertwinerDeterminantPolynomial_ne_zero
    (rho : Representation F G V) (sigma : Representation F G W)
    (bV : Module.Basis ι F V) (bW : Module.Basis ι F W)
    (b : Module.Basis κ F (rho →ₗ sigma))
    (hp : intertwinerDeterminantPolynomial rho sigma bV bW b ≠ 0) :
    Nonempty (rho ≃ₗ sigma) := by
  classical
  obtain ⟨x, hx⟩ :=
    exists_aeval_ne_zero_algebraicClosure
      (intertwinerDeterminantPolynomial rho sigma bV bW b) hp
  let S := IntermediateField.adjoin F (Set.range x)
  let y : κ → S := fun k =>
    ⟨x k, IntermediateField.subset_adjoin F (Set.range x) ⟨k, rfl⟩⟩
  let : FiniteDimensional F S :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isIntegral (K := F)).1 z
  have hy : MvPolynomial.aeval y
      (intertwinerDeterminantPolynomial rho sigma bV bW b) ≠ 0 := by
    intro hzero
    apply hx
    calc
      MvPolynomial.aeval x
          (intertwinerDeterminantPolynomial rho sigma bV bW b) =
          MvPolynomial.aeval (fun k => S.val (y k))
            (intertwinerDeterminantPolynomial rho sigma bV bW b) := by
              rfl
      _ = S.val (MvPolynomial.aeval y
            (intertwinerDeterminantPolynomial rho sigma bV bW b)) :=
          (MvPolynomial.comp_aeval_apply y S.val
            (intertwinerDeterminantPolynomial rho sigma bV bW b)).symm
      _ = 0 := by rw [hzero, map_zero]
  exact repEquiv_of_finite_extension rho sigma
    (repEquiv_of_aeval_intertwinerDeterminantPolynomial_ne_zero
      rho sigma bV bW b y hy)

/-- If finite-dimensional representations become equivalent after an
arbitrary scalar extension, then they were already equivalent. -/
public theorem repEquiv_of_extendScalars
    {S : Type*} [Field S] [Algebra F S]
    (rho : Representation F G V) (sigma : Representation F G W)
    (hS : Nonempty (extendScalars S rho ≃ₗ extendScalars S sigma)) :
    Nonempty (rho ≃ₗ sigma) := by
  classical
  let eS := Classical.choice hS
  have hdim : Module.finrank F V = Module.finrank F W := by
    rw [← Module.finrank_baseChange (R := S) (S := F) (M' := V),
      ← Module.finrank_baseChange (R := S) (S := F) (M' := W)]
    exact eS.toLinearEquiv.finrank_eq
  let bV : Module.Basis (Fin (Module.finrank F V)) F V :=
    Module.finBasis F V
  let bW : Module.Basis (Fin (Module.finrank F V)) F W :=
    (Module.finBasis F W).reindex (finCongr hdim.symm)
  let : Module F (rho →ₗ sigma) := Theory.Representation.RepMap.instModule rho sigma
  let : Module.Finite F (rho →ₗ sigma) :=
    Module.Finite.of_injective
      (IntertwiningMap.toLinearMapl (ρ := rho) (σ := sigma))
      (IntertwiningMap.toLinearMap_injective rho sigma)
  let : Module.Free F (rho →ₗ sigma) :=
    @Module.Free.of_divisionRing F (rho →ₗ sigma) _ _
      (Theory.Representation.RepMap.instModule rho sigma)
  let b : Module.Basis (Fin (Module.finrank F (rho →ₗ sigma))) F
      (rho →ₗ sigma) := Module.finBasis F (rho →ₗ sigma)
  let q := intertwiningMapBaseChangeEquiv (E := S) rho sigma
  obtain ⟨z, hz⟩ := q.surjective eS.toRepMap
  let x : Fin (Module.finrank F (rho →ₗ sigma)) → S :=
    fun k => (b.baseChange S).repr z k
  have hsum :
      (∑ k, x k • extendScalars_map S (b k)) = eS.toRepMap := by
    rw [← hz]
    calc
      (∑ k, x k • extendScalars_map S (b k)) =
          ∑ k, q (x k • (b.baseChange S k)) := by
            apply Finset.sum_congr rfl
            intro k _
            simp [q, Module.Basis.baseChange_apply,
              intertwiningMapBaseChangeEquiv_tmul]
      _ = q (∑ k, x k • (b.baseChange S k)) := by
            rw [map_sum]
      _ = q z := by rw [(b.baseChange S).sum_repr z]
  let p := intertwinerDeterminantPolynomial rho sigma bV bW b
  have hpEval : MvPolynomial.aeval x p ≠ 0 := by
    dsimp only [p]
    rw [aeval_intertwinerDeterminantPolynomial]
    have hmap :
        (∑ k, x k • LinearMap.baseChange S (b k).toLinearMap) =
          eS.toLinearMap := by
      calc
        (∑ k, x k • LinearMap.baseChange S (b k).toLinearMap) =
            IntertwiningMap.toLinearMapl
              (ρ := extendScalars S rho) (σ := extendScalars S sigma)
              (∑ k, x k • extendScalars_map S (b k)) := by
                rw [map_sum]
                apply Finset.sum_congr rfl
                intro k _
                change x k • LinearMap.baseChange S (b k).toLinearMap =
                  x k • (extendScalars_map S (b k)).toLinearMap
                rw [extendScalars_map_toLinearMap]
        _ = IntertwiningMap.toLinearMapl
              (ρ := extendScalars S rho) (σ := extendScalars S sigma)
              eS.toRepMap := by
                exact congrArg
                  (IntertwiningMap.toLinearMapl
                    (ρ := extendScalars S rho) (σ := extendScalars S sigma)) hsum
        _ = eS.toLinearMap := rfl
    rw [hmap]
    exact (eS.toLinearEquiv.isUnit_det (bV.baseChange S)
      (bW.baseChange S)).ne_zero
  have hp : p ≠ 0 := by
    intro hzero
    apply hpEval
    rw [hzero, map_zero]
  exact repEquiv_of_intertwinerDeterminantPolynomial_ne_zero
    rho sigma bV bW b hp
end DeterminantSpecialization
end CFSG.Theory.Representation
