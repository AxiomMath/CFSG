module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped TensorProduct MonoidAlgebra

private lemma w183_asAlgebraHom_comp {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (φ : V →ₗ[ZMod 2] V)
    (hφ : ∀ g v, φ (ρ g v) = ρ g (φ v)) :
    ∀ (a : MonoidAlgebra (ZMod 2) G) (v : V),
      φ (ρ.asAlgebraHom a v) = ρ.asAlgebraHom a (φ v) := by
  intro a v
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | single g r =>
    simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul, hφ]

private lemma w183_asModuleEquiv_apply {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (v : Representation.asModule ρ) : ρ.asModuleEquiv v = v := rfl

private lemma w183_comm_forward {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (γ : G ≃* G)
    (φ : Module.End (MonoidAlgebra (ZMod 2) G)
      (Representation.asModule (ρ.comp γ.toMonoidHom))) (g : G)
    (v : Representation.asModule (ρ.comp γ.toMonoidHom)) :
    φ (ρ g v) = ρ g (φ v) := by
  have h := φ.map_smul (MonoidAlgebra.single (γ.symm g) (1 : ZMod 2)) v
  rw [Representation.single_smul, Representation.single_smul] at h
  simpa only [w183_asModuleEquiv_apply, one_smul, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using h

private noncomputable def w183_endToHom {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (γ : G ≃* G) :
    Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom)) →+*
      Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule where
  toFun φ :=
    { toFun := fun v => φ v
      map_add' := fun v w => map_add φ v w
      map_smul' := fun a v =>
        w183_asAlgebraHom_comp ρ (φ.restrictScalars (ZMod 2))
          (fun g v => w183_comm_forward ρ γ φ g v) a v }
  map_one' := by ext v; rfl
  map_mul' := by intro φ ψ; ext v; rfl
  map_zero' := by ext v; rfl
  map_add' := by intro φ ψ; ext v; rfl

private lemma w183_comm_backward {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (γ : G ≃* G)
    (ψ : Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) (g : G)
    (v : Representation.asModule ρ) :
    ψ ((ρ.comp γ.toMonoidHom) g v) = (ρ.comp γ.toMonoidHom) g (ψ v) := by
  have h := ψ.map_smul (MonoidAlgebra.single (γ g) (1 : ZMod 2)) v
  rw [Representation.single_smul, Representation.single_smul] at h
  simpa only [w183_asModuleEquiv_apply, one_smul, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom] using h

private noncomputable def w183_endFromHom {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (γ : G ≃* G) :
    Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule →+*
      Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom)) where
  toFun ψ :=
    { toFun := fun v => ψ v
      map_add' := fun v w => map_add ψ v w
      map_smul' := fun a v =>
        w183_asAlgebraHom_comp (ρ.comp γ.toMonoidHom) (ψ.restrictScalars (ZMod 2))
          (fun g v => w183_comm_backward ρ γ ψ g v) a v }
  map_one' := by ext v; rfl
  map_mul' := by intro φ ψ; ext v; rfl
  map_zero' := by ext v; rfl
  map_add' := by intro φ ψ; ext v; rfl

private noncomputable def w183_endEquiv {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (γ : G ≃* G) :
    Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom)) ≃+*
      Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule where
  toFun := w183_endToHom ρ γ
  invFun := w183_endFromHom ρ γ
  left_inv := fun φ => by ext v; rfl
  right_inv := fun ψ => by ext v; rfl
  map_mul' := map_mul (w183_endToHom ρ γ)
  map_add' := map_add (w183_endToHom ρ γ)

private noncomputable def w183_tensorEquiv
    {E E' k M : Type*} [CommRing E] [CommRing E'] [Field k]
    [Algebra E k] [Algebra E' k] [AddCommGroup M] [Module E M] [Module E' M]
    (e : E' ≃+* E) (halg : ∀ φ' : E', algebraMap E' k φ' = algebraMap E k (e φ'))
    (hM : ∀ (φ' : E') (m : M), φ' • m = (e φ') • m) :
    (k ⊗[E'] M) ≃ₗ[k] (k ⊗[E] M) := by
  have keyF : ∀ (φ' : E') (c : k) (m : M),
      φ' • (c ⊗ₜ[E] m) = (φ' • c) ⊗ₜ[E] m := by
    intro φ' c m
    rw [TensorProduct.smul_tmul']
  have keyB : ∀ (ψ : E) (c : k) (m : M),
      ψ • (c ⊗ₜ[E'] m) = (ψ • c) ⊗ₜ[E'] m := by
    intro ψ c m
    rw [TensorProduct.smul_tmul']
  have hkeyF : ∀ (φ' : E') (c : k) (m : M),
      ((e φ') • c) ⊗ₜ[E] m = φ' • (c ⊗ₜ[E] m) := by
    intro φ' c m
    rw [keyF φ' c m]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def, halg φ']
  have hkeyB : ∀ (ψ : E) (c : k) (m : M),
      ((e.symm ψ) • c) ⊗ₜ[E'] m = ψ • (c ⊗ₜ[E'] m) := by
    intro ψ c m
    rw [keyB ψ c m]
    congr 1
    rw [Algebra.smul_def, halg (e.symm ψ), e.apply_symm_apply, Algebra.smul_def]
  let f : k →ₗ[E'] M →ₗ[E'] (k ⊗[E] M) :=
    { toFun := fun c =>
        { toFun := fun m => c ⊗ₜ[E] m
          map_add' := fun m₁ m₂ => TensorProduct.tmul_add c m₁ m₂
          map_smul' := fun φ' m => by
            calc c ⊗ₜ[E] (φ' • m)
                = c ⊗ₜ[E] ((e φ') • m) := by rw [hM φ' m]
              _ = ((e φ') • c) ⊗ₜ[E] m := TensorProduct.tmul_smul (e φ') c m
              _ = φ' • (c ⊗ₜ[E] m) := hkeyF φ' c m }
      map_add' := fun c₁ c₂ => by ext m; exact TensorProduct.add_tmul c₁ c₂ m
      map_smul' := fun φ' c => by
        ext m
        exact (keyF φ' c m).symm }
  let g : k →ₗ[E] M →ₗ[E] (k ⊗[E'] M) :=
    { toFun := fun c =>
        { toFun := fun m => c ⊗ₜ[E'] m
          map_add' := fun m₁ m₂ => TensorProduct.tmul_add c m₁ m₂
          map_smul' := fun ψ m => by
            have h1 : (e.symm ψ) • m = ψ • m := by
              simpa only [e.apply_symm_apply] using hM (e.symm ψ) m
            calc c ⊗ₜ[E'] (ψ • m)
                = c ⊗ₜ[E'] ((e.symm ψ) • m) := by rw [h1]
              _ = ((e.symm ψ) • c) ⊗ₜ[E'] m := TensorProduct.tmul_smul (e.symm ψ) c m
              _ = ψ • (c ⊗ₜ[E'] m) := hkeyB ψ c m }
      map_add' := fun c₁ c₂ => by ext m; exact TensorProduct.add_tmul c₁ c₂ m
      map_smul' := fun ψ c => by
        ext m
        exact (keyB ψ c m).symm }
  let θF : (k ⊗[E'] M) →ₗ[k] (k ⊗[E] M) :=
    { toFun := TensorProduct.lift f
      map_add' := fun x y => map_add (TensorProduct.lift f) x y
      map_smul' := fun a x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul c m =>
            change TensorProduct.lift f (a • (c ⊗ₜ[E'] m)) =
              a • TensorProduct.lift f (c ⊗ₜ[E'] m)
            rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
            change (a • c) ⊗ₜ[E] m = a • (c ⊗ₜ[E] m)
            rw [TensorProduct.smul_tmul']
        | add x y hx hy => simp [map_add, hx, hy] }
  let θB : (k ⊗[E] M) →ₗ[k] (k ⊗[E'] M) :=
    { toFun := TensorProduct.lift g
      map_add' := fun x y => map_add (TensorProduct.lift g) x y
      map_smul' := fun a x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul c m =>
            change TensorProduct.lift g (a • (c ⊗ₜ[E] m)) =
              a • TensorProduct.lift g (c ⊗ₜ[E] m)
            rw [TensorProduct.smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul]
            change (a • c) ⊗ₜ[E'] m = a • (c ⊗ₜ[E'] m)
            rw [TensorProduct.smul_tmul']
        | add x y hx hy => simp [map_add, hx, hy] }
  have hθF' : ∀ (c : k) (m : M), θF (c ⊗ₜ[E'] m) = c ⊗ₜ[E] m := fun c m => rfl
  have hθB' : ∀ (c : k) (m : M), θB (c ⊗ₜ[E] m) = c ⊗ₜ[E'] m := fun c m => rfl
  refine LinearEquiv.ofLinear θF θB ?_ ?_
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => rw [LinearMap.comp_apply, hθB' c m, hθF' c m, LinearMap.id_coe, id_eq]
    | add x y hx hy => simp [map_add, hx, hy]
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => rw [LinearMap.comp_apply, hθF' c m, hθB' c m, LinearMap.id_coe, id_eq]
    | add x y hx hy => simp [map_add, hx, hy]

theorem exists_extendScalars_comp_equiv {G : Type} [Group G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    [ρ.IsIrreducible] (γ : G ≃* G) [Representation.IsIrreducible (ρ.comp γ.toMonoidHom)]
    {k : Type} [Field k] [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k] :
    ∃ (_ : Algebra (Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom))) k)
      (θ : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G)
          (Representation.asModule (ρ.comp γ.toMonoidHom))]
          (Representation.asModule (ρ.comp γ.toMonoidHom))) ≃ₗ[k]
        (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule)),
      ∀ (g : G) (v : k ⊗[Module.End (MonoidAlgebra (ZMod 2) G)
          (Representation.asModule (ρ.comp γ.toMonoidHom))]
          (Representation.asModule (ρ.comp γ.toMonoidHom))),
        θ (CFSG.Theory.Representation.extendScalars k
            (CFSG.endFieldRep (ρ.comp γ.toMonoidHom)) g v) =
          CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) (γ g) (θ v) := by
  let e : Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom)) ≃+*
      Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule := w183_endEquiv ρ γ
  letI : Algebra (Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom))) k :=
    ((algebraMap (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k).comp
      e.toRingHom).toAlgebra
  letI : Module (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule)
      (Representation.asModule (ρ.comp γ.toMonoidHom)) :=
    Module.compHom (Representation.asModule (ρ.comp γ.toMonoidHom)) e.symm.toRingHom
  have halg : ∀ φ' : Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom)),
      algebraMap (Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom))) k φ' =
      algebraMap (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k (e φ') :=
    fun φ' => rfl
  have hM : ∀ (φ' : Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom)))
        (m : Representation.asModule (ρ.comp γ.toMonoidHom)),
      φ' • m = (e φ') • m := fun φ' m => rfl
  let θ : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom))]
        (Representation.asModule (ρ.comp γ.toMonoidHom))) ≃ₗ[k]
      (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule) :=
    w183_tensorEquiv e halg hM
  have hθ : ∀ (c : k) (m : Representation.asModule (ρ.comp γ.toMonoidHom)),
      θ (c ⊗ₜ[Module.End (MonoidAlgebra (ZMod 2) G)
        (Representation.asModule (ρ.comp γ.toMonoidHom))] m) =
      c ⊗ₜ[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] m := fun c m => rfl
  refine ⟨inferInstance, θ, ?_⟩
  intro g
  have hcomp :
      θ.toLinearMap.comp
          (CFSG.Theory.Representation.extendScalars k
            (CFSG.endFieldRep (ρ.comp γ.toMonoidHom)) g) =
        (CFSG.Theory.Representation.extendScalars k
            (CFSG.endFieldRep ρ) (γ g)).comp θ.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c m
    change θ ((CFSG.Theory.Representation.extendScalars k
          (CFSG.endFieldRep (ρ.comp γ.toMonoidHom)) g)
            (c ⊗ₜ[Module.End (MonoidAlgebra (ZMod 2) G)
              (Representation.asModule (ρ.comp γ.toMonoidHom))] m)) =
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) (γ g))
        (θ (c ⊗ₜ[Module.End (MonoidAlgebra (ZMod 2) G)
          (Representation.asModule (ρ.comp γ.toMonoidHom))] m))
    conv_lhs =>
      rw [CFSG.Theory.Representation.extendScalars_apply, LinearMap.baseChange_tmul, hθ]
    conv_rhs =>
      rw [hθ, CFSG.Theory.Representation.extendScalars_apply]
      change c ⊗ₜ[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule]
        ((CFSG.endFieldRep ρ) (γ g) m)
    rfl
  intro v
  exact LinearMap.congr_fun hcomp v

end CFSG.LocalAnalysis.WeakClosure81
