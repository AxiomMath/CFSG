module

public import Mathlib.RepresentationTheory.Irreducible

namespace CFSG
end CFSG
open CFSG

open _root_.Representation
open scoped MonoidAlgebra

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

public theorem OrderIso.isAtomistic_of_isAtomistic [OrderBot α] [OrderBot β] (f : α ≃o β) :
    IsAtomistic α → IsAtomistic β := fun hα => ⟨fun b => by
  rcases hα with ⟨hα⟩
  rcases hα (f.symm b) with ⟨Sα, ⟨hα1, hα2⟩⟩
  use (f '' Sα)
  constructor
  · constructor
    · simp only [upperBounds, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq]
      exact fun _ h => (le_symm_apply f).mp (hα1.1 h)
    · simp only [lowerBounds, upperBounds, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq]
      intro b' ha
      have := @hα1.2 (f.symm b')
      rw [map_le_map_iff] at this
      exact this fun a' ha' => (le_symm_apply f).mpr (ha a' ha')
  · simpa only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, isAtom_iff] using hα2⟩

namespace Subrepresentation

section completeLattice

variable {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V] [Module F V]
  {ρ : Representation F G V}

public instance : InfSet (Subrepresentation ρ) :=
  ⟨fun S ↦ Subrepresentation.mk (⨅ s ∈ S, s.toSubmodule) <| fun g v hv => by
    simp only [Submodule.mem_iInf] at ⊢ hv
    exact fun s hs => s.apply_mem_toSubmodule g (hv s hs)⟩

public theorem sInf_le' {S : Set (Subrepresentation ρ)} {p} : p ∈ S → sInf S ≤ p := fun hp => by
  suffices h : (⨅ s ∈ S, s.toSubmodule) ≤ p.toSubmodule by exact le_of_le_of_eq h rfl
  exact iInf₂_le p hp

public theorem le_sInf' {S : Set (Subrepresentation ρ)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S := fun hq => by
  suffices h : p.toSubmodule ≤ (⨅ s ∈ S, s.toSubmodule) by exact le_of_le_of_eq h rfl
  exact le_iInf₂_iff.mpr hq

public instance completeLattice : CompleteLattice (Subrepresentation ρ) :=
{   (inferInstance : OrderTop (Subrepresentation ρ)),
    (inferInstance : OrderBot (Subrepresentation ρ)) with
    sup := fun a b ↦ sInf { x | a ≤ x ∧ b ≤ x }
    le_sup_left := fun _ _ ↦ le_sInf' fun _ ⟨h, _⟩ ↦ h
    le_sup_right := fun _ _ ↦ le_sInf' fun _ ⟨_, h⟩ ↦ h
    sup_le := fun _ _ _ h₁ h₂ ↦ sInf_le' ⟨h₁, h₂⟩
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ ↦ Set.subset_inter
    inf_le_left := fun _ _ ↦ Set.inter_subset_left
    inf_le_right := fun _ _ ↦ Set.inter_subset_right
    sSup S := sInf {sm | ∀ s ∈ S, s ≤ sm}
    isLUB_sSup := fun _ ↦ ⟨fun s h ↦ le_sInf' fun _ a ↦ a s h,
      fun _ x ↦ sInf_le' x⟩
    isGLB_sInf := fun _ ↦ ⟨fun _ h ↦ sInf_le' h,
      fun _ x ↦ le_sInf' x⟩ }

end completeLattice

section Nontrivial

variable {F G V : Type*} [CommRing F] [Monoid G] [AddCommMonoid V] [Module F V]
  {ρ : Representation F G V}

public instance module_nontrival [Nontrivial V] : Nontrivial (Subrepresentation ρ) where
  exists_pair_ne := ⟨⊤, ⊥, by
    have : (⊤ : Subrepresentation ρ).toSubmodule ≠ ⊥ := by calc
      _ = ⊤ := rfl
      _ ≠ _ := top_ne_bot
    exact fun a ↦ this (congrArg _ a)⟩

variable {F G V : Type*} [Field F] [Monoid G] [AddCommGroup V] [Module F V]
  (ρ : Representation F G V)

public theorem irreducible_module_nontrivial [inst : IsIrreducible ρ] : Nontrivial V where
  exists_pair_ne := by
    by_contra! h
    exact inst.bot_ne_top (isMax_iff_eq_top.mp fun _ _ x _ ↦ h x 0)


end Nontrivial

section IsAtomic

variable {F G V : Type*} [Field F] [Monoid G] [AddCommGroup V] [Module F V]
  {ρ : Representation F G V} (φ : Subrepresentation ρ)

public theorem irreducible_iff_isAtom : IsIrreducible φ.toRepresentation ↔ IsAtom φ := by
  unfold IsIrreducible
  rw [isSimpleOrder_iff_isAtom_top]
  let f : (Set.Iic φ) ≃o (Subrepresentation φ.toRepresentation) := {
    toFun := fun s => (.mk (Submodule.comap φ.toSubmodule.subtype s.val.toSubmodule) (fun g v hv => by
        simp only [Submodule.mem_comap, Submodule.subtype_apply] at ⊢ hv
        apply apply_mem_toSubmodule
        exact Submodule.mem_comap.mp hv))
    invFun := fun s => ⟨.mk (Submodule.map φ.toSubmodule.subtype s.toSubmodule) (fun g v hv => by
        simp only [Submodule.mem_map, Submodule.subtype_apply, Subtype.exists, exists_and_right,
          exists_eq_right] at ⊢ hv
        rcases hv with ⟨hv1, hv2⟩
        exact ⟨φ.apply_mem_toSubmodule g hv1, s.apply_mem_toSubmodule g hv2⟩),
      Set.mem_Iic.mpr (Submodule.map_subtype_le φ.toSubmodule s.toSubmodule)⟩
    left_inv := fun s => by
      rw [← Subtype.val_inj]
      apply Subrepresentation.toSubmodule_injective
      simp only [Submodule.map_comap_subtype, inf_eq_right]
      exact s.prop
    right_inv := fun s => by
      simp only
      apply Subrepresentation.toSubmodule_injective
      simp only [Submodule.comap_map_eq, Submodule.ker_subtype, bot_le, sup_of_le_left]
    map_rel_iff' := by
      simp only [Equiv.coe_fn_mk, Subtype.forall, Set.mem_Iic, Subtype.mk_le_mk]
      intro s₁ hs₁ s₂ hs₂
      have : Submodule.comap φ.toSubmodule.subtype s₁.toSubmodule ≤ Submodule.comap φ.toSubmodule.subtype s₂.toSubmodule ↔ s₁ ≤ s₂ := by
        have (s : Subrepresentation ρ) : φ.toSubmodule ⊓ s.toSubmodule = (φ ⊓ s).toSubmodule := rfl
        simp only [Submodule.comap_subtype_le_iff, this, hs₁, hs₂, inf_of_le_right]
        rfl
      exact this
  }
  let φ' : Set.Iic φ := ⟨φ, le_refl φ⟩
  have : f φ' = ⊤ := (map_eq_top_iff f).mpr rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply IsAtom.of_isAtom_coe_Iic (a := φ')
    rw [← OrderIso.isAtom_iff f, this]
    exact h
  · have h : IsAtom φ' := IsAtom.Iic h (le_refl φ)
    rw [← this, OrderIso.isAtom_iff]
    exact h

variable [FiniteDimensional F V]

public instance isAtomic_of_finite_dimensional : IsAtomic (Subrepresentation ρ) := by
  refine ⟨?_⟩
  intro φ
  by_cases hφ : φ = ⊥
  · left
    exact hφ
  right
  let p : ℕ → Prop := fun n => ∃ ψ : Subrepresentation ρ, ψ ≤ φ ∧ ψ ≠ ⊥ ∧ Module.finrank F ψ.toSubmodule = n
  have hp : ∃ n, p n := ⟨Module.finrank F φ.1, φ, le_refl φ, hφ, rfl⟩
  have : DecidablePred p := by exact Classical.decPred p
  rcases Nat.find_spec hp with ⟨ψ, hψle, hψn, hψdim⟩
  refine ⟨ψ, ⟨hψn, fun χ hχlt => ?_⟩, hψle⟩
  by_contra! h
  exact Nat.find_min hp (hψdim ▸ Submodule.finrank_lt_finrank_of_lt hχlt) ⟨χ, le_trans (le_of_lt hχlt) hψle, h, rfl⟩

public theorem irreducible_subrepresentation_of_finite_dimensional (ρ : Representation F G V) [Nontrivial V] : ∃ (φ : Subrepresentation ρ), IsIrreducible φ.toRepresentation := by
  rcases IsAtomic.exists_atom (Subrepresentation ρ) with ⟨φ, hφ⟩
  exact ⟨φ, (irreducible_iff_isAtom φ).mpr hφ⟩

variable [IsSemisimpleRing F[G]]

set_option backward.isDefEq.respectTransparency false in
public instance isAtomistic_of_finite_dimensional_semisimple : IsAtomistic (Subrepresentation ρ) :=
OrderIso.isAtomistic_of_isAtomistic subrepresentationSubmoduleOrderIso.symm inferInstance

end IsAtomic

end Subrepresentation
