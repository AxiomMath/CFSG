module

public import CFSG.Monster.B.TwoA.Fischer.SplitAffineM22Core
public import CFSG.Monster.B.Fischer.HexadCode

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem clique_split_pinned_M22_affine_action
    {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] (η : C ≃ X₀)
    (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    (φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀)
    (hφgen : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    (hφ : ∀ (f : setStab act lab Y C) (r : Subgroup.closure (lab '' C))
      (h : (f : S) * r * (f : S)⁻¹ ∈ Subgroup.closure (lab '' C)),
      φ (Additive.ofMul ⟨(f : S) * r * (f : S)⁻¹, h⟩) = rhoW (θ f) (φ (Additive.ofMul r))) :
    (∀ x ∈ hexadFiber lab Y C ∅, ∀ y ∈ hexadFiber lab Y C ∅,
      ∃! r, r ∈ ptStab act lab Y C ∧ act r x = y) ∧
    ∀ x ∈ hexadFiber lab Y C ∅,
      ((ptStab act lab Y C).subgroupOf (setStab act lab Y C)).IsComplement'
        ((setStab act lab Y C ⊓ actStab act x).subgroupOf (setStab act lab Y C)) ∧
      (∃ eK : ↥(setStab act lab Y C ⊓ actStab act x) ≃* CFSG.Blueprint.NativeSporadic.M22,
        (∀ k, eK k = θ (Subgroup.inclusion inf_le_left k)) ∧
        ∀ (k : ↥(setStab act lab Y C ⊓ actStab act x)) (z : C),
          (η (setStabPerm act lab Y C (Subgroup.inclusion inf_le_left k) z) : Fin 24) =
            psiHom (eK k) (η z)) ∧
      ∃ (Ψ : ↥(setStab act lab Y C) ≃*
          Multiplicative W₀ ⋊[repMulAut rhoW] CFSG.Blueprint.NativeSporadic.M22)
        (c : ↥(hexadFiber lab Y C ∅) ≃ W₀),
        (∀ (r : Subgroup.closure (lab '' C)) (k : S)
          (hk : k ∈ setStab act lab Y C ⊓ actStab act x)
          (h : (r : S) * k ∈ setStab act lab Y C),
          Ψ ⟨(r : S) * k, h⟩ = ⟨Multiplicative.ofAdd (φ (Additive.ofMul r)),
            θ (QuotientGroup.mk (⟨k, hk.1⟩ : setStab act lab Y C))⟩) ∧
        (∀ (r : Subgroup.closure (lab '' C)) (h : act (r : S) x ∈ hexadFiber lab Y C ∅),
          c ⟨act (r : S) x, h⟩ = φ (Additive.ofMul r)) ∧
        (∀ (z : C) (h : act (lab z) x ∈ hexadFiber lab Y C ∅),
          c ⟨act (lab z) x, h⟩ = K₀.mkQ (e (η z))) ∧
        ∀ (f : setStab act lab Y C) (y : ↥(hexadFiber lab Y C ∅))
          (h : act (f : S) y ∈ hexadFiber lab Y C ∅),
          c ⟨act (f : S) y, h⟩ = Multiplicative.toAdd (Ψ f).left + rhoW (Ψ f).right (c y) := by
  obtain ⟨-, hreg, hx'⟩ := hS.clique_split_regular hC
  refine ⟨hreg, fun x hx => ?_⟩
  obtain ⟨⟨eK, heK⟩, Ψ, c, hΨ, hc, haff⟩ := hS.clique_split_affine_core hC rhoW θ φ hφ hx
  refine ⟨(hx' x hx).1, ⟨eK, heK, fun k z => by rw [heK]; exact hθ _ z⟩, Ψ, c, hΨ, hc,
    fun z h => ?_, haff⟩
  rw [← hφgen z]
  exact hc (cliqueGen z) h

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
