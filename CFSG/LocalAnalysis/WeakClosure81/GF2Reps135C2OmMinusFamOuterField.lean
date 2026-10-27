module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
import CFSG.Quasithin.H13.NQTermLinearThreeTools
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped TensorProduct

private noncomputable def w135c2_omfMField_transport {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (T : V →ₗ[ZMod 2] V) :
    ρ.asModule →ₗ[ZMod 2] ρ.asModule :=
  (ρ.asModuleEquiv.symm : ρ.asModule ≃ₗ[ZMod 2] V).toLinearMap ∘ₗ T ∘ₗ
    (ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod 2] V).toLinearMap

@[simp] private theorem w135c2_omfMField_transport_apply {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (T : V →ₗ[ZMod 2] V) (x : ρ.asModule) :
    w135c2_omfMField_transport ρ T x = ρ.asModuleEquiv.symm (T (ρ.asModuleEquiv x)) := rfl

private theorem w135c2_omfMField_transport_smul {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (T : V →ₗ[ZMod 2] V)
    (hT : ∀ f : V →ₗ[ZMod 2] V, (∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) → T ∘ₗ f = f ∘ₗ T)
    (c : Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) (x : ρ.asModule) :
    w135c2_omfMField_transport ρ T (c • x) = c • w135c2_omfMField_transport ρ T x := by
  classical
  have hsingle : ∀ (g : G) (y : ρ.asModule),
      (MonoidAlgebra.single g (1 : ZMod 2) : MonoidAlgebra (ZMod 2) G) • y =
        CFSG.endFieldRep ρ g y := by
    intro g y
    apply ρ.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, CFSG.endFieldRep_apply']
    simp
  have hcG : ∀ (g : G) (y : ρ.asModule), c (CFSG.endFieldRep ρ g y) =
      CFSG.endFieldRep ρ g (c y) := by
    intro g y
    calc c (CFSG.endFieldRep ρ g y)
        = c ((MonoidAlgebra.single g (1 : ZMod 2) : MonoidAlgebra (ZMod 2) G) • y) := by
          rw [hsingle]
      _ = (MonoidAlgebra.single g (1 : ZMod 2) : MonoidAlgebra (ZMod 2) G) • c y :=
          c.map_smul _ _
      _ = CFSG.endFieldRep ρ g (c y) := hsingle g (c y)
  let f : V →ₗ[ZMod 2] V :=
    (ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod 2] V).toLinearMap ∘ₗ c ∘ₗ
      (ρ.asModuleEquiv.symm : ρ.asModule ≃ₗ[ZMod 2] V).toLinearMap
  have hf : ∀ g : G, f ∘ₗ ρ g = ρ g ∘ₗ f := by
    intro g
    ext w
    change ρ.asModuleEquiv (c (ρ.asModuleEquiv.symm (ρ g w))) =
      ρ g (ρ.asModuleEquiv (c (ρ.asModuleEquiv.symm w)))
    have hw : ρ.asModuleEquiv.symm (ρ g w) =
        CFSG.endFieldRep ρ g (ρ.asModuleEquiv.symm w) := by
      rw [CFSG.endFieldRep_apply, LinearEquiv.apply_symm_apply]
    rw [hw, hcG, CFSG.endFieldRep_apply']
  apply ρ.asModuleEquiv.injective
  calc ρ.asModuleEquiv (w135c2_omfMField_transport ρ T (c • x))
      = T (ρ.asModuleEquiv (c • x)) := by simp [w135c2_omfMField_transport_apply]
    _ = T (f (ρ.asModuleEquiv x)) := by simp [f]
    _ = f (T (ρ.asModuleEquiv x)) := by
        have h := congrArg (fun l : V →ₗ[ZMod 2] V => l (ρ.asModuleEquiv x)) (hT f hf)
        simpa [LinearMap.comp_apply] using h
    _ = ρ.asModuleEquiv (c • w135c2_omfMField_transport ρ T x) := by
        simp [f, w135c2_omfMField_transport_apply]

private theorem w135c2_omfMField_commute_of_endRing {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (T : V →ₗ[ZMod 2] V)
    (hcomm : ∀ d : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ, ∀ v, T (d v) = d (T v)) :
    ∀ f : V →ₗ[ZMod 2] V, (∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) → T ∘ₗ f = f ∘ₗ T := by
  intro f hf
  obtain ⟨d, hd⟩ :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.mem_endRing_iff ρ f).mpr fun g v => by
      have h := congrArg (fun m : V →ₗ[ZMod 2] V => m v) (hf g)
      simpa [LinearMap.comp_apply] using h
  ext v
  have h := hcomm d v
  rw [congrFun hd v, congrFun hd (T v)] at h
  simpa [LinearMap.comp_apply] using h

private theorem w135c2_omfMField_baseChange_intertwine {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (k : Type) [Field k]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k]
    (σ : Representation (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) G ρ.asModule)
    (T_E : ρ.asModule →ₗ[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule)
    (α : G → G) (hTE : ∀ g x, T_E (σ g x) = σ (α g) (T_E x)) :
    ∀ (g : G) (u : k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule),
      (T_E.baseChange k) (CFSG.Theory.Representation.extendScalars k σ g u) =
        CFSG.Theory.Representation.extendScalars k σ (α g) ((T_E.baseChange k) u) := by
  intro g u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
      rw [CFSG.Theory.Representation.extendScalars_apply,
        CFSG.Theory.Representation.extendScalars_apply]
      calc (T_E.baseChange k) ((σ g).baseChange k (c ⊗ₜ x))
          = (T_E.baseChange k) (c ⊗ₜ σ g x) := by rw [LinearMap.baseChange_tmul]
        _ = c ⊗ₜ T_E (σ g x) := by rw [LinearMap.baseChange_tmul]
        _ = c ⊗ₜ σ (α g) (T_E x) := by rw [hTE g x]
        _ = (σ (α g)).baseChange k (c ⊗ₜ T_E x) := by rw [LinearMap.baseChange_tmul]
        _ = (σ (α g)).baseChange k ((T_E.baseChange k) (c ⊗ₜ x)) := by congr 1
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]

private theorem w135c2_omfMField_finrank_le_restrictScalars {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    [ρ.IsIrreducible]
    (W : Submodule (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) ρ.asModule) :
    Module.finrank (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) W ≤
      Module.finrank (ZMod 2) (W.restrictScalars (ZMod 2)) := by
  let E := Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule
  have htower := Module.finrank_mul_finrank (ZMod 2) E (W.restrictScalars (ZMod 2))
  have heq : Module.finrank E (W.restrictScalars (ZMod 2)) = Module.finrank E W :=
    (Submodule.restrictScalarsEquiv (ZMod 2) E ρ.asModule W).finrank_eq
  have hpos : 0 < Module.finrank (ZMod 2) E := Module.finrank_pos
  calc Module.finrank E W
      = Module.finrank E (W.restrictScalars (ZMod 2)) := heq.symm
    _ = 1 * Module.finrank E (W.restrictScalars (ZMod 2)) := (one_mul _).symm
    _ ≤ Module.finrank (ZMod 2) E * Module.finrank E (W.restrictScalars (ZMod 2)) :=
        Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr hpos.ne')
    _ = Module.finrank (ZMod 2) (W.restrictScalars (ZMod 2)) := htower

private theorem w135c2_omfMField_finrank_range_baseChange_eq {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    [ρ.IsIrreducible] (k : Type) [Field k]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k]
    (T_E : ρ.asModule →ₗ[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule) :
    Module.finrank k (LinearMap.range ((T_E.baseChange k) - 1)) =
      Module.finrank (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule)
        (LinearMap.range (T_E - 1)) := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule
  have : FiniteDimensional E ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  have hsub : T_E.baseChange k - 1 = (T_E - 1).baseChange k := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]
  rw [hsub]
  exact CFSG.Quasithin.H13.NQTerm.finrank_range_baseChange (K := E) (E := k) (T_E - 1)

private theorem w135c2_omfMField_finrank_range_restrictScalars_eq {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    [ρ.IsIrreducible] (T : V →ₗ[ZMod 2] V)
    (T_E : ρ.asModule →ₗ[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule)
    (he_TE : ∀ x, ρ.asModuleEquiv (T_E x) = T (ρ.asModuleEquiv x)) :
    Module.finrank (ZMod 2) ((LinearMap.range (T_E - 1)).restrictScalars (ZMod 2)) =
      Module.finrank (ZMod 2) (LinearMap.range (T - 1)) := by
  classical
  have hcomp : (ρ.asModuleEquiv : ρ.asModule →ₗ[ZMod 2] V) ∘ₗ
      ((T_E : ρ.asModule →ₗ[ZMod 2] ρ.asModule) - 1) =
      (T - 1) ∘ₗ (ρ.asModuleEquiv : ρ.asModule →ₗ[ZMod 2] V) := by
    ext x
    change ρ.asModuleEquiv (T_E x) - ρ.asModuleEquiv x =
      T (ρ.asModuleEquiv x) - ρ.asModuleEquiv x
    rw [he_TE]
  have hWrs : (LinearMap.range (T_E - 1)).restrictScalars (ZMod 2) =
      LinearMap.range ((T_E : ρ.asModule →ₗ[ZMod 2] ρ.asModule) - 1) :=
    Submodule.ext fun _ => Iff.rfl
  have hmap : Submodule.map (ρ.asModuleEquiv : ρ.asModule →ₗ[ZMod 2] V)
      ((LinearMap.range (T_E - 1)).restrictScalars (ZMod 2)) = LinearMap.range (T - 1) := by
    rw [hWrs, ← LinearMap.range_comp
        ((T_E : ρ.asModule →ₗ[ZMod 2] ρ.asModule) - 1)
        (ρ.asModuleEquiv : ρ.asModule →ₗ[ZMod 2] V),
      hcomp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod 2] V).surjective,
      Submodule.map_top]
  rw [← hmap]
  exact (LinearEquiv.finrank_map_eq (ρ.asModuleEquiv : ρ.asModule ≃ₗ[ZMod 2] V)
    ((LinearMap.range (T_E - 1)).restrictScalars (ZMod 2))).symm

private theorem w135c2_omfMField_finrank_range_baseChange_le {G V : Type} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    [ρ.IsIrreducible] (k : Type) [Field k]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k]
    (T : V →ₗ[ZMod 2] V)
    (T_E : ρ.asModule →ₗ[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule)
    (he_TE : ∀ x, ρ.asModuleEquiv (T_E x) = T (ρ.asModuleEquiv x)) :
    Module.finrank k (LinearMap.range ((T_E.baseChange k) - 1)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (T - 1)) := by
  let E := Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule
  calc Module.finrank k (LinearMap.range ((T_E.baseChange k) - 1))
      = Module.finrank E (LinearMap.range (T_E - 1)) :=
        w135c2_omfMField_finrank_range_baseChange_eq ρ k T_E
    _ ≤ Module.finrank (ZMod 2) ((LinearMap.range (T_E - 1)).restrictScalars (ZMod 2)) :=
        w135c2_omfMField_finrank_le_restrictScalars ρ (LinearMap.range (T_E - 1))
    _ = Module.finrank (ZMod 2) (LinearMap.range (T - 1)) :=
        w135c2_omfMField_finrank_range_restrictScalars_eq ρ T T_E he_TE

theorem exists_extendScalars_endField_intertwiner {G : Type} [Group G] [Finite G] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    [ρ.IsIrreducible] (k : Type) [Field k]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) k] (T : V →ₗ[ZMod 2] V)
    (α : G → G) (hT : ∀ (g : G) (v : V), T (ρ g v) = ρ (α g) (T v))
    (hcomm : ∀ (d : CFSG.QuasithinUnique.Setup.SL2Modules.EndRing ρ) (v : V),
      T (d v) = d (T v)) :
    ∃ T' : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule) →ₗ[k]
        (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule),
      (∀ (g : G) (u : k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule] ρ.asModule),
        T' (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g u) =
          CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) (α g) (T' u)) ∧
      Module.finrank k (LinearMap.range (T' - 1)) ≤
        Module.finrank (ZMod 2) (LinearMap.range (T - 1)) := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule
  have hTcomm : ∀ f : V →ₗ[ZMod 2] V, (∀ g, f ∘ₗ ρ g = ρ g ∘ₗ f) → T ∘ₗ f = f ∘ₗ T :=
    w135c2_omfMField_commute_of_endRing ρ T hcomm
  let T_E : ρ.asModule →ₗ[E] ρ.asModule :=
    { toFun := fun x => ρ.asModuleEquiv.symm (T (ρ.asModuleEquiv x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun c x => by
        change w135c2_omfMField_transport ρ T (c • x) =
          c • w135c2_omfMField_transport ρ T x
        exact w135c2_omfMField_transport_smul ρ T hTcomm c x }
  have hTE_apply (x : ρ.asModule) :
      T_E x = ρ.asModuleEquiv.symm (T (ρ.asModuleEquiv x)) := rfl
  have he_TE (x : ρ.asModule) :
      ρ.asModuleEquiv (T_E x) = T (ρ.asModuleEquiv x) := by
    rw [hTE_apply, LinearEquiv.apply_symm_apply]
  have hTE : ∀ g x, T_E (CFSG.endFieldRep ρ g x) = CFSG.endFieldRep ρ (α g) (T_E x) := by
    intro g x
    apply ρ.asModuleEquiv.injective
    rw [CFSG.endFieldRep_apply', hTE_apply, hTE_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, CFSG.endFieldRep_apply']
    exact hT g (ρ.asModuleEquiv x)
  refine ⟨T_E.baseChange k, ?_, ?_⟩
  · exact w135c2_omfMField_baseChange_intertwine ρ k (CFSG.endFieldRep ρ) T_E α hTE
  · exact w135c2_omfMField_finrank_range_baseChange_le ρ k T T_E he_TE

end CFSG.LocalAnalysis.WeakClosure81
