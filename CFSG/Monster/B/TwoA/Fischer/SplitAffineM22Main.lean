module

public import CFSG.Monster.B.TwoA.Fischer.SplitAffineM22
public import CFSG.Monster.B.TwoA.Fischer.CliqueModule

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

theorem clique_split_pinned_M22
    {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] (η : C ≃ X₀)
    (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22)
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    (φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀)
    (hφgen : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) :
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
          c ⟨act (f : S) y, h⟩ = Multiplicative.toAdd (Ψ f).left + rhoW (Ψ f).right (c y) :=
  hS.clique_split_pinned_M22_affine_action hC η θ hθ φ hφgen
    ((hS.clique_exact_binary_M22_module hC η θ hη hθ).2.2.1 φ hφgen)

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
