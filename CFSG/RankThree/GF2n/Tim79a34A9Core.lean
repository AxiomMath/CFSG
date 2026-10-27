module

public import CFSG.RankThree.GF2n.Tim79a34Forms
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtendScalars
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.RankThree.GF2n.Tim79a

@[expose] def A9AbsIrrStatement : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 9)) U), Function.Injective ρ →
    Module.finrank (ZMod 2) U = 8 → CFSG.Theory.Representation.IsAbsolutelyIrreducible ρ

@[expose] def Tim79aF2Eight : Type := Fin 8 → ZMod 2

instance : AddCommGroup Tim79aF2Eight := inferInstanceAs (AddCommGroup (Fin 8 → ZMod 2))

instance : Module (ZMod 2) Tim79aF2Eight := inferInstanceAs (Module (ZMod 2) (Fin 8 → ZMod 2))

instance : FiniteDimensional (ZMod 2) Tim79aF2Eight :=
  inferInstanceAs (Module.Finite (ZMod 2) (Fin 8 → ZMod 2))

theorem perm_hom_eq_one {L X : Type*} [Group L] [Finite X] (hX : Nat.card X ≤ 4)
    (hL : commutator L = ⊤) (π : L →* Equiv.Perm X) : π = 1 := by
  obtain ⟨n, hn⟩ := (Equiv.Perm.isSolvable (α := X) hX).solvable
  have hmap : (⊤ : Subgroup L).map π = ⁅(⊤ : Subgroup L).map π, (⊤ : Subgroup L).map π⁆ := by
    have hL' : (⁅(⊤ : Subgroup L), ⊤⁆ : Subgroup L) = ⊤ := hL
    calc (⊤ : Subgroup L).map π = (⁅(⊤ : Subgroup L), ⊤⁆ : Subgroup L).map π := by rw [hL']
      _ = ⁅(⊤ : Subgroup L).map π, (⊤ : Subgroup L).map π⁆ := by
        rw [Subgroup.map_commutator]
  have hle : ∀ m : ℕ, (⊤ : Subgroup L).map π ≤ derivedSeries (Equiv.Perm X) m := by
    intro m
    induction m with
    | zero =>
      rw [derivedSeries_zero]
      exact le_top
    | succ m ih =>
      rw [derivedSeries_succ]
      exact (le_of_eq hmap).trans (Subgroup.commutator_mono ih ih)
  have hbot : (⊤ : Subgroup L).map π ≤ ⊥ := by
    have h := hle n
    rwa [hn] at h
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply, ← Subgroup.mem_bot]
  exact hbot (Subgroup.mem_map.mpr ⟨g, Subgroup.mem_top g, rfl⟩)

@[expose] def actPerm {L A : Type*} [Group L] [AddCommGroup A] [Module (ZMod 2) A]
    (ρA : Representation (ZMod 2) L A) : L →* Equiv.Perm A where
  toFun g :=
    { toFun := ρA g
      invFun := ρA g⁻¹
      left_inv := fun x => by
        change ρA g⁻¹ (ρA g x) = x
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := fun x => by
        change ρA g (ρA g⁻¹ x) = x
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }
  map_one' := Equiv.ext fun x => by
    change ρA 1 x = x
    rw [map_one, Module.End.one_apply]
  map_mul' g h := Equiv.ext fun x => by
    change ρA (g * h) x = ρA g (ρA h x)
    rw [map_mul, Module.End.mul_apply]

@[expose] def conjRep {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (e : V ≃ₗ[ZMod 2] W)
    (ρ : Representation (ZMod 2) G V) : Representation (ZMod 2) G W where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by
    ext w
    simp
  map_mul' g h := by
    ext w
    simp [map_mul, Module.End.mul_apply]

@[expose] def conjRepEquiv {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (e : V ≃ₗ[ZMod 2] W)
    (ρ : Representation (ZMod 2) G V) :
    CFSG.Theory.Representation.RepEquiv ρ (conjRep e ρ) :=
  CFSG.Theory.Representation.RepEquiv.mk e fun g => by
    ext v
    simp [conjRep]

theorem conjRep_injective {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (e : V ≃ₗ[ZMod 2] W)
    {ρ : Representation (ZMod 2) G V} (hρ : Function.Injective ρ) :
    Function.Injective (conjRep e ρ) := by
  intro g h hgh
  apply hρ
  ext v
  have h1 := LinearMap.congr_fun hgh (e v)
  simpa [conjRep] using h1

theorem isAbsolutelyIrreducible_iff_of_repEquiv {F G V W : Type*} [Field F] [Monoid G]
    [AddCommGroup V] [AddCommGroup W] [Module F V] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (f : CFSG.Theory.Representation.RepEquiv ρ σ) :
    CFSG.Theory.Representation.IsAbsolutelyIrreducible ρ ↔
      CFSG.Theory.Representation.IsAbsolutelyIrreducible σ := by
  let f' : CFSG.Theory.Representation.RepEquiv
      (CFSG.Theory.Representation.extendScalars (AlgebraicClosure F) ρ)
      (CFSG.Theory.Representation.extendScalars (AlgebraicClosure F) σ) :=
    CFSG.Theory.Representation.RepEquiv.mk
      (LinearEquiv.baseChange F (AlgebraicClosure F) V W f.toLinearEquiv) fun g => by
        have h := congrArg (LinearMap.baseChange (AlgebraicClosure F)) (f.isIntertwining' g)
        rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h
        exact h
  rw [CFSG.Theory.Representation.isAbsolutelyIrreducible_iff ρ,
    CFSG.Theory.Representation.isAbsolutelyIrreducible_iff σ]
  exact CFSG.Theory.Representation.RepEquiv.irreducible_euqiv f'

theorem no_A9_of_equivariant_pairing (hI : A9AbsIrrStatement)
    {L U A : Type*} [Group L] [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (e : L ≃* alternatingGroup (Fin 9)) (ρ : Representation (ZMod 2) L U)
    (hρ : Function.Injective ρ) (hU : Module.finrank (ZMod 2) U = 8)
    (hA : Module.finrank (ZMod 2) A = 2) (ρA : Representation (ZMod 2) L A)
    (κ : U →ₗ[ZMod 2] U →ₗ[ZMod 2] A) (hκ : ∀ (g : L) (x y : U), κ (ρ g x) (ρ g y) = ρA g (κ x y))
    (hspan : ∀ l : Module.Dual (ZMod 2) A, (∀ x y, l (κ x y) = 0) → l = 0) : False := by
  have hcardA : Nat.card A = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hA]
    simp
  have hA9 : commutator (alternatingGroup (Fin 9)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hA9perf : Group.IsPerfect (alternatingGroup (Fin 9)) := Group.isPerfect_def.mpr hA9
  have hLperf : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hL : commutator L = ⊤ := Group.isPerfect_def.mp hLperf
  haveI : Finite A := Module.finite_of_finite (ZMod 2)
  have hρA1 : ∀ g : L, ρA g = 1 := by
    intro g
    have hπ : actPerm ρA = 1 := perm_hom_eq_one hcardA.le hL (actPerm ρA)
    have hg : actPerm ρA g = 1 := DFunLike.congr_fun hπ g
    ext x
    exact congrArg (fun p : Equiv.Perm A => p x) hg
  have hκinv : ∀ (g : L) (x y : U), κ (ρ g x) (ρ g y) = κ x y := by
    intro g x y
    have h := hκ g x y
    rw [hρA1 g, Module.End.one_apply] at h
    exact h
  let ρ9 : Representation (ZMod 2) (alternatingGroup (Fin 9)) U := ρ.comp e.symm.toMonoidHom
  have hρ9 : Function.Injective ρ9 := by
    intro g h hgh
    have hgh' : ρ (e.symm g) = ρ (e.symm h) := hgh
    exact e.symm.injective (hρ hgh')
  have hκ9 : ∀ (g : alternatingGroup (Fin 9)) (x y : U), κ (ρ9 g x) (ρ9 g y) = κ x y :=
    fun g x y => hκinv (e.symm g) x y
  have hfin8 : Module.finrank (ZMod 2) Tim79aF2Eight = 8 := Module.finrank_fin_fun (ZMod 2)
  let e8 : U ≃ₗ[ZMod 2] Tim79aF2Eight :=
    LinearEquiv.ofFinrankEq U Tim79aF2Eight (by rw [hU, hfin8])
  let ρ8 : Representation (ZMod 2) (alternatingGroup (Fin 9)) Tim79aF2Eight :=
    conjRep e8 ρ9
  have hρ8 : Function.Injective ρ8 := conjRep_injective e8 hρ9
  have hirr8 : CFSG.Theory.Representation.IsAbsolutelyIrreducible ρ8 :=
    hI Tim79aF2Eight ρ8 hρ8 hfin8
  have hirr9 : CFSG.Theory.Representation.IsAbsolutelyIrreducible ρ9 :=
    (isAbsolutelyIrreducible_iff_of_repEquiv (conjRepEquiv e8 ρ9)).mpr hirr8
  haveI := hirr9
  exact no_invariant_bilinear_map_onto_plane ρ9 κ hκ9 hspan hA

end CFSG.RankThree.GF2n.Tim79a

end
