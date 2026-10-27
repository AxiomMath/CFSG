module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Induced
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv

namespace CFSG
end CFSG
open CFSG

open _root_.Representation
open scoped MonoidAlgebra

namespace CFSG.Theory.Representation

variable {F G V : Type*} [Group G] [Field F] [AddCommGroup V] [Module F V] {H : Subgroup G} [hH : H.Normal] (ρ : Representation F H V)

/-- The conjugate representation of `ρ` by the element `x`. -/
@[expose]
public def conjugateRep (x : G) : Representation F H V := {
  toFun := fun h => ρ (⟨x * h.val * x⁻¹, Subgroup.Normal.conj_mem hH h h.prop x⟩)
  map_one' := by
    simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel]
    rw [(Subgroup.mk_eq_one _).mpr rfl, map_one]
  map_mul' := fun g₁ g₂ => by
    rw[← map_mul]
    simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk, conj_mul]
}

public theorem conjugateRep_apply (x : G) (h : H) : (conjugateRep ρ x) h = ρ (⟨x * h.val * x⁻¹, Subgroup.Normal.conj_mem hH h h.prop x⟩) := rfl


/-- Transport a subrepresentation of a normal subgroup through the inverse of an
ambient representation operator. -/
@[expose] public def conjugateSubrepresentation
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (W : Subrepresentation (rho.comp H.subtype)) (g : G) :
    Subrepresentation (rho.comp H.subtype) where
  toSubmodule := Submodule.map (rho g⁻¹) W.toSubmodule
  apply_mem_toSubmodule h v hv := by
    rcases hv with ⟨w, hw, rfl⟩
    let h' : H :=
      ⟨g * (h : G) * g⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 g⟩
    refine ⟨rho h' w, W.apply_mem_toSubmodule h' hw, ?_⟩
    change rho g⁻¹ (rho (h' : G) w) = rho (h : G) (rho g⁻¹ w)
    simp [h', map_mul, Module.End.mul_eq_comp, mul_assoc]

@[simp]
public theorem conjugateSubrepresentation_toSubmodule
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (W : Subrepresentation (rho.comp H.subtype)) (g : G) :
    (conjugateSubrepresentation rho H W g).toSubmodule =
      Submodule.map (rho g⁻¹) W.toSubmodule := rfl

/-- The transported subrepresentation is equivalent to the corresponding
conjugate representation. -/
public noncomputable def conjugateSubrepresentationEquiv
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (W : Subrepresentation (rho.comp H.subtype)) (g : G) :
    (conjugateSubrepresentation rho H W g).toRepresentation ≃ₗ
      Theory.Representation.conjugateRep (G := G) (H := H) W.toRepresentation g := by
  let Wg := conjugateSubrepresentation rho H W g
  let L : Wg.toSubmodule →ₗ[F] W.toSubmodule := {
    toFun := fun x => by
      refine ⟨rho g x.1, ?_⟩
      rcases x.2 with ⟨w, hw, hx⟩
      rw [← hx]
      simpa [map_mul, Module.End.mul_eq_comp] using hw
    map_add' := by
      intro x y
      ext
      simp
    map_smul' := by
      intro c x
      ext
      simp }
  refine Theory.Representation.RepEquiv.mk (LinearEquiv.ofBijective L ?_) ?_
  · constructor
    · intro x y hxy
      apply Subtype.ext
      exact (Representation.apply_bijective rho g).1 (congrArg Subtype.val hxy)
    · intro y
      refine ⟨⟨rho g⁻¹ y.1, ?_⟩, ?_⟩
      · exact ⟨y.1, y.2, rfl⟩
      · apply Subtype.ext
        simp [L]
  · intro h
    ext x
    change rho g (rho (h : G) x.1) = rho (g * (h : G) * g⁻¹) (rho g x.1)
    simp [map_mul, Module.End.mul_eq_comp, mul_assoc]

/-- A representation equivalence induces an equivalence between the
corresponding conjugate representations. -/
public noncomputable def conjugateRepEquiv
    {F G V W : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {H : Subgroup G} [H.Normal]
    {rho : Representation F H V} {sigma : Representation F H W}
    (e : rho ≃ₗ sigma) (g : G) :
    Theory.Representation.conjugateRep (G := G) (H := H) rho g ≃ₗ
      Theory.Representation.conjugateRep (G := G) (H := H) sigma g := by
  refine Theory.Representation.RepEquiv.mk e.toLinearEquiv ?_
  intro h
  ext v
  simp only [LinearMap.comp_apply, Theory.Representation.conjugateRep_apply]
  have he : (e.toLinearEquiv : V → W) = (e : V → W) :=
    Theory.Representation.RepEquiv.coe_toLinearMap e
  simp only [LinearEquiv.coe_toLinearMap]
  rw [he]
  simpa [Theory.Representation.conjugateRep_apply] using
    Theory.Representation.RepEquiv.isIntertwining e
      ⟨g * (h : G) * g⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.2 g⟩ v
/-- Conjugation by an ambient representation operator is an order automorphism
of the lattice of subrepresentations of a normal subgroup. -/
public noncomputable def conjugateSubrepresentationOrderIso
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal] (g : G) :
    Subrepresentation (rho.comp H.subtype) ≃o
      Subrepresentation (rho.comp H.subtype) where
  toFun W := conjugateSubrepresentation rho H W g⁻¹
  invFun W := conjugateSubrepresentation rho H W g
  left_inv W := by
    apply Subrepresentation.toSubmodule_injective
    rw [conjugateSubrepresentation_toSubmodule,
      conjugateSubrepresentation_toSubmodule]
    rw [← W.toSubmodule.map_comp]
    simp [← Module.End.mul_eq_comp, ← map_mul, Module.End.one_eq_id]
  right_inv W := by
    apply Subrepresentation.toSubmodule_injective
    rw [conjugateSubrepresentation_toSubmodule,
      conjugateSubrepresentation_toSubmodule]
    rw [← W.toSubmodule.map_comp]
    simp [← Module.End.mul_eq_comp, ← map_mul, Module.End.one_eq_id]
  map_rel_iff' := by
    intro W U
    change
      (conjugateSubrepresentation rho H W g⁻¹ ≤
          conjugateSubrepresentation rho H U g⁻¹) ↔ W ≤ U
    change
      (conjugateSubrepresentation rho H W g⁻¹).toSubmodule ≤
          (conjugateSubrepresentation rho H U g⁻¹).toSubmodule ↔
        W.toSubmodule ≤ U.toSubmodule
    rw [conjugateSubrepresentation_toSubmodule,
      conjugateSubrepresentation_toSubmodule]
    have hinj : Function.Injective (rho g) := by
      intro x y hxy
      have hxy' := congrArg (rho g⁻¹) hxy
      simpa [← Module.End.mul_apply, ← map_mul] using hxy'
    simpa only [inv_inv] using
      (Submodule.map_le_map_iff_of_injective
        hinj W.toSubmodule U.toSubmodule)


@[simp]
public theorem conjugateSubrepresentationOrderIso_toSubmodule
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (g : G) (W : Subrepresentation (rho.comp H.subtype)) :
    (conjugateSubrepresentationOrderIso rho H g W).toSubmodule =
      Submodule.map (rho g) W.toSubmodule := by
  change Submodule.map (rho (g⁻¹)⁻¹) W.toSubmodule =
    Submodule.map (rho g) W.toSubmodule
  rw [inv_inv]

@[simp]
public theorem conjugateSubrepresentationOrderIso_apply
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (g : G) (W : Subrepresentation (rho.comp H.subtype)) :
    conjugateSubrepresentationOrderIso rho H g W =
      conjugateSubrepresentation rho H W g⁻¹ := by
  apply Subrepresentation.toSubmodule_injective
  rw [conjugateSubrepresentationOrderIso_toSubmodule,
    conjugateSubrepresentation_toSubmodule, inv_inv]

@[simp]
public theorem conjugateSubrepresentationOrderIso_one
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (W : Subrepresentation (rho.comp H.subtype)) :
    conjugateSubrepresentationOrderIso rho H 1 W = W := by
  apply Subrepresentation.toSubmodule_injective
  rw [conjugateSubrepresentationOrderIso_toSubmodule, map_one,
    Module.End.one_eq_id, Submodule.map_id]

@[simp]
public theorem conjugateSubrepresentationOrderIso_mul
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    (g k : G) (W : Subrepresentation (rho.comp H.subtype)) :
    conjugateSubrepresentationOrderIso rho H (g * k) W =
      conjugateSubrepresentationOrderIso rho H g
        (conjugateSubrepresentationOrderIso rho H k W) := by
  apply Subrepresentation.toSubmodule_injective
  rw [conjugateSubrepresentationOrderIso_toSubmodule,
    conjugateSubrepresentationOrderIso_toSubmodule,
    conjugateSubrepresentationOrderIso_toSubmodule]
  rw [← W.toSubmodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul]

/-- Transport an equivalence of subrepresentations through the same ambient
conjugation operator. -/
public noncomputable def conjugateSubrepresentationOrderIsoRepEquiv
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (H : Subgroup G) [H.Normal]
    {U W : Subrepresentation (rho.comp H.subtype)}
    (e : U.toRepresentation ≃ₗ W.toRepresentation) (g : G) :
    (conjugateSubrepresentationOrderIso rho H g U).toRepresentation ≃ₗ
      (conjugateSubrepresentationOrderIso rho H g W).toRepresentation :=
  (conjugateSubrepresentationEquiv rho H U g⁻¹).trans
    ((conjugateRepEquiv e g⁻¹).trans
      (conjugateSubrepresentationEquiv rho H W g⁻¹).symm)
-- TODO : M^x ≅ M ⨂ x

end CFSG.Theory.Representation
