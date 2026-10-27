module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RepresentationTheory

open Matrix

variable {F G : Type*} [Field F] [Group G] {d : ℕ}

@[expose] def IsIrreducibleMatrixRep (ρ : G →* GL (Fin d) F) : Prop :=
  ∀ W : Submodule F (Fin d → F), (∀ g, ∀ w ∈ W, (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W) →
    W = ⊥ ∨ W = ⊤

@[expose] def matrixOrbit (ρ : G →* GL (Fin d) F) (w : Fin d → F) : Set (Fin d → F) :=
  Set.range fun g => (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w

@[expose] def matrixVecStabilizer (ρ : G →* GL (Fin d) F) (w : Fin d → F) : Subgroup G where
  carrier := {g | (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w = w}
  mul_mem' {a b} ha hb := by
    change (ρ (a * b) : Matrix (Fin d) (Fin d) F) *ᵥ w = w
    rw [map_mul, Units.val_mul, ← mulVec_mulVec, hb, ha]
  one_mem' := by
    change (ρ 1 : Matrix (Fin d) (Fin d) F) *ᵥ w = w
    rw [map_one, Units.val_one, one_mulVec]
  inv_mem' {a} ha := by
    change (ρ a⁻¹ : Matrix (Fin d) (Fin d) F) *ᵥ w = w
    conv_lhs => rw [← ha]
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      one_mulVec]

theorem mem_matrixVecStabilizer {ρ : G →* GL (Fin d) F} {w : Fin d → F} {g : G} :
    g ∈ matrixVecStabilizer ρ w ↔ (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w = w :=
  Iff.rfl

theorem stabilizer_class_invariant_of_twist_isomorphic [Finite G] (ρ : G →* GL (Fin d) F)
    (v : Fin d → F)
    (htwist : ∀ α : MulAut G, ∃ P : GL (Fin d) F, ∀ g, ρ (α g) = P * ρ g * P⁻¹)
    (horbit : ∀ w : Fin d → F,
      Nat.card (matrixOrbit ρ w) = Nat.card (matrixOrbit ρ v) → matrixOrbit ρ w = matrixOrbit ρ v)
    (α : MulAut G) :
    ∃ k : G, (matrixVecStabilizer ρ v).map α.toMonoidHom =
      (matrixVecStabilizer ρ v).map (MulAut.conj k).toMonoidHom := by
  obtain ⟨P, hP⟩ := htwist α
  set w := (P : Matrix (Fin d) (Fin d) F) *ᵥ v with hw
  have hact : ∀ g, (ρ (α g) : Matrix (Fin d) (Fin d) F) *ᵥ w =
      (P : Matrix (Fin d) (Fin d) F) *ᵥ ((ρ g : Matrix (Fin d) (Fin d) F) *ᵥ v) := by
    intro g
    rw [hP, hw, mulVec_mulVec, mulVec_mulVec, Units.val_mul, Units.val_mul, mul_assoc,
      Units.inv_mul, mul_one]
  have hPinj : Function.Injective fun u : Fin d → F => (P : Matrix (Fin d) (Fin d) F) *ᵥ u := by
    intro u u' h
    have := congrArg (fun z => ((P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ z) h
    simpa only [mulVec_mulVec, Units.inv_mul, one_mulVec] using this
  have himage : matrixOrbit ρ w =
      (fun u => (P : Matrix (Fin d) (Fin d) F) *ᵥ u) '' matrixOrbit ρ v := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨(ρ (α.symm h) : Matrix (Fin d) (Fin d) F) *ᵥ v, ⟨α.symm h, rfl⟩, ?_⟩
      dsimp only
      rw [← hact, MulEquiv.apply_symm_apply]
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨α g, hact g⟩
  have hcard : Nat.card (matrixOrbit ρ w) = Nat.card (matrixOrbit ρ v) := by
    rw [himage]
    exact Nat.card_image_of_injective hPinj _
  have hwX : w ∈ matrixOrbit ρ v := by
    rw [← horbit w hcard]
    refine ⟨1, ?_⟩
    dsimp only
    rw [map_one, Units.val_one, one_mulVec]
  obtain ⟨k, hk⟩ := hwX
  refine ⟨k, ?_⟩
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, mem_matrixVecStabilizer,
    mem_matrixVecStabilizer]
  have h1 : (ρ (α.symm x) : Matrix (Fin d) (Fin d) F) *ᵥ v = v ↔
      (ρ x : Matrix (Fin d) (Fin d) F) *ᵥ w = w := by
    have := hact (α.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [this, hw]
    exact hPinj.eq_iff.symm
  have h2 : (ρ ((MulAut.conj k).symm x) : Matrix (Fin d) (Fin d) F) *ᵥ v = v ↔
      (ρ x : Matrix (Fin d) (Fin d) F) *ᵥ w = w := by
    rw [MulAut.conj_symm_apply, ← hk, mulVec_mulVec, ← Units.val_mul, ← map_mul]
    constructor
    · intro h
      calc (ρ (x * k) : Matrix (Fin d) (Fin d) F) *ᵥ v
          = (ρ k : Matrix (Fin d) (Fin d) F) *ᵥ
              ((ρ (k⁻¹ * x * k) : Matrix (Fin d) (Fin d) F) *ᵥ v) := by
            rw [mulVec_mulVec, ← Units.val_mul, ← map_mul]
            congr 3
            group
        _ = (ρ k : Matrix (Fin d) (Fin d) F) *ᵥ v := by rw [h]
    · intro h
      calc (ρ (k⁻¹ * x * k) : Matrix (Fin d) (Fin d) F) *ᵥ v
          = (ρ k⁻¹ : Matrix (Fin d) (Fin d) F) *ᵥ
              ((ρ (x * k) : Matrix (Fin d) (Fin d) F) *ᵥ v) := by
            rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_assoc]
        _ = (ρ k⁻¹ : Matrix (Fin d) (Fin d) F) *ᵥ ((ρ k : Matrix (Fin d) (Fin d) F) *ᵥ v) := by
            rw [h]
        _ = v := by
            rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
              Units.val_one, one_mulVec]
  rw [h1, h2]

theorem unique_vector_orbit_module_twisting_class_invariance [Finite F] (_hd : 1 ≤ d)
    [Finite G] (ρ : G →* GL (Fin d) F) (hρ : Function.Injective ρ)
    (hirr : IsIrreducibleMatrixRep ρ)
    (huniq : ∀ ρ' : G →* GL (Fin d) F, Function.Injective ρ' → IsIrreducibleMatrixRep ρ' →
      ∃ P : GL (Fin d) F, ∀ g, ρ' g = P * ρ g * P⁻¹)
    (v : Fin d → F)
    (horbit : ∀ w : Fin d → F,
      Nat.card (matrixOrbit ρ w) = Nat.card (matrixOrbit ρ v) → matrixOrbit ρ w = matrixOrbit ρ v)
    (α : MulAut G) :
    ∃ k : G, (matrixVecStabilizer ρ v).map α.toMonoidHom =
      (matrixVecStabilizer ρ v).map (MulAut.conj k).toMonoidHom := by
  refine stabilizer_class_invariant_of_twist_isomorphic ρ v (fun β => ?_) horbit α
  refine huniq (ρ.comp β.toMonoidHom) (hρ.comp β.injective) (fun W hW => hirr W ?_)
  intro g w hw
  have := hW (β.symm g) w hw
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    using this

end CFSG.RepresentationTheory
