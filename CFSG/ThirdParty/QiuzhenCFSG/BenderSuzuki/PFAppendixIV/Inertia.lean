module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEnd
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
public import Mathlib.FieldTheory.Fixed

namespace CFSG
end CFSG
open CFSG

/-!
# Inertia groups and endomorphism-algebra transport
-/

noncomputable section

namespace CFSG.BenderSuzuki
namespace PFAppendixIV

universe u v w
/-- The identity element gives the canonical equivalence with the corresponding conjugate representation. -/
public noncomputable def conjugateRep_equiv_one
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) :
    rho ≃ₗ Theory.Representation.conjugateRep rho (1 : G) := by
  refine Theory.Representation.RepEquiv.mk (LinearEquiv.refl F V) ?_
  intro h
  ext x
  simp [Theory.Representation.conjugateRep_apply]

/-- Transport a conjugacy equivalence after conjugating both representations on the right. -/
public noncomputable def conjugateRep_equiv_mul_left
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) {a g : G}
    (e : rho ≃ₗ Theory.Representation.conjugateRep rho a) :
    Theory.Representation.conjugateRep rho g ≃ₗ
      Theory.Representation.conjugateRep rho (a * g) := by
  refine Theory.Representation.RepEquiv.mk e.toLinearEquiv ?_
  intro h
  ext x
  change e (rho ⟨g * h * g⁻¹,
    Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⟩ x) =
      rho ⟨(a * g) * h * (a * g)⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop (a * g)⟩ (e x)
  simpa only [Theory.Representation.conjugateRep_apply, mul_inv_rev, mul_assoc] using
    Theory.Representation.RepEquiv.isIntertwining e
      ⟨g * h * g⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : H.Normal) h h.prop g⟩ x

/-- Move an equivalence between two conjugates back to the original representation. -/
public noncomputable def conjugateRep_diff_equiv
    {F : Type v} [Field F] {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) {g x : G}
    (e : Theory.Representation.conjugateRep rho g ≃ₗ
      Theory.Representation.conjugateRep rho x) :
    rho ≃ₗ Theory.Representation.conjugateRep rho (x * g⁻¹) := by
  refine Theory.Representation.RepEquiv.mk e.toLinearEquiv ?_
  intro h
  ext y
  let h' : H := ⟨g⁻¹ * h * g, by
    simpa using (inferInstance : H.Normal).conj_mem (h : G) h.2 g⁻¹⟩
  change e (rho h y) = (Theory.Representation.conjugateRep rho (x * g⁻¹)) h (e y)
  simpa only [h', Theory.Representation.conjugateRep_apply, LinearMap.comp_apply,
    mul_inv_rev, inv_inv, mul_inv_cancel, mul_inv_cancel_left, mul_inv_cancel_right,
    mul_one, mul_assoc] using
    (Theory.Representation.RepEquiv.isIntertwining e h' y)

/-- The subgroup stabilizing the isomorphism class of a representation of a normal subgroup. -/
public noncomputable def representationInertiaSubgroup
    {F : Type v} [Field F] {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) : Subgroup G where
  carrier := {g | Nonempty (rho ≃ₗ Theory.Representation.conjugateRep rho g)}
  one_mem' := ⟨conjugateRep_equiv_one rho⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ea⟩ := ha
    obtain ⟨eb⟩ := hb
    exact ⟨eb.trans
      (conjugateRep_equiv_mul_left rho (g := b) ea)⟩
  inv_mem' := by
    intro a ha
    obtain ⟨ea⟩ := ha
    let eone := conjugateRep_equiv_one rho
    exact ⟨by
      simpa using
        (conjugateRep_diff_equiv rho (g := a) (x := 1)
          (ea.symm.trans eone))⟩

@[simp] public theorem mem_representationInertiaSubgroup_iff
    {F : Type v} [Field F] {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {V : Type u} [AddCommGroup V] [Module F V]
    (rho : Representation F H V) (g : G) :
    g ∈ representationInertiaSubgroup H rho ↔
      Nonempty (rho ≃ₗ Theory.Representation.conjugateRep rho g) := Iff.rfl


end PFAppendixIV
end CFSG.BenderSuzuki
