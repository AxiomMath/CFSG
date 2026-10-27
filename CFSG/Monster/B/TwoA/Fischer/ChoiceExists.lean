module

public import CFSG.Monster.B.TwoA.Fischer.FullIntertwinerMain
public import CFSG.Monster.B.TwoA.Fischer.SplitAffineM22Main
public import CFSG.Monster.B.TwoA.Fischer.AdjointIntertwiner
public import CFSG.Monster.B.TwoA.Fischer.CliqueM22

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std
open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

variable (act lab Y) in
@[expose] def HasAdmissibleChoice
    (C : Set V)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] : Prop :=
  ∃ x ∈ hexadFiber lab Y C ∅, ∃ (η : C ≃ X₀)
    (θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22),
    (∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀) ∧
    (∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z)) ∧
    ∃ φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀,
    (∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) ∧
    ∃ α : setStab act lab Y C →* F₀,
    (∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k)) ∧
    ∃ Φ : Y ≃ CFSG.Monster.B.Fischer.Y, IsCliqueIntertwiner act lab Y C x η φ α Φ

theorem repMulAut_rhoW_apply_eq_wAut
    (g : CFSG.Blueprint.NativeSporadic.M22) :
    (MonoidHom.id (Multiplicative W₀)).comp (repMulAut rhoW g).toMonoidHom =
      (wAut ((MonoidHom.id CFSG.Blueprint.NativeSporadic.M22) g)).toMonoidHom.comp
        (MonoidHom.id (Multiplicative W₀)) := by
  ext w
  rfl

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem exists_mem_hexadFiber_empty {C : Set V} (hC : IsSliceMaxClique lab Y C) :
    ∃ x, x ∈ hexadFiber lab Y C ∅ := by
  obtain ⟨_, -, -, -, -, -, -, -, -, -, h1024, -⟩ := hS.clique_hexad_fibers hC
  exact Set.nonempty_of_ncard_ne_zero (by rw [h1024]; decide)

theorem exists_alpha
    {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
    (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z))) :
    ∃ α : setStab act lab Y C →* F₀, ∀ (r : Subgroup.closure (lab '' C))
      (f k : setStab act lab Y C), (f : S) = r * k → act (k : S) x = x →
        α f = wF (φ (Additive.ofMul r)) * kF (θ k) := by
  obtain ⟨-, hsplit⟩ := hS.clique_split_pinned_M22 hC η θ hη hθ φ hφ
  obtain ⟨-, -, Ψ, -, hΨ, -⟩ := hsplit x hx
  refine ⟨(SemidirectProduct.map (MonoidHom.id _) (MonoidHom.id _)
    repMulAut_rhoW_apply_eq_wAut).comp Ψ.toMonoidHom, fun r f k hf hk => ?_⟩
  have hkF : (k : S) ∈ setStab act lab Y C ⊓ actStab act x := ⟨k.2, hk⟩
  have hmem : (r : S) * k ∈ setStab act lab Y C := hf ▸ f.2
  have h1 := hΨ r (k : S) hkF hmem
  have hf' : f = ⟨(r : S) * k, hmem⟩ := Subtype.ext hf
  subst hf'
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
  exact (SemidirectProduct.inl_left_mul_inr_right
    (⟨Multiplicative.ofAdd (φ (Additive.ofMul r)), θ k⟩ : F₀)).symm

theorem hasAdmissibleChoice
    {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] :
    HasAdmissibleChoice act lab Y C := by
  obtain ⟨x, hx⟩ := hS.exists_mem_hexadFiber_empty hC
  obtain ⟨η, θ, hη, hθ, -⟩ := hS.clique_catalog_M22_quotient hC
  obtain ⟨φ, hφ, -⟩ := (hS.clique_exact_binary_M22_module hC η θ hη hθ).2.1
  obtain ⟨α, hα⟩ := hS.exists_alpha hC hx hη hθ hφ
  obtain ⟨Φ, hΦ, -⟩ := hS.full_clique_action_intertwiner' hC hx hη hθ hφ hα
  unfold HasAdmissibleChoice
  exact ⟨x, hx, η, θ, hη, hθ, φ, hφ, α, hα, Φ, hΦ⟩

theorem exists_cliqueData :
    ∃ C : Set V, IsSliceMaxClique lab Y C ∧
      ∃ _ : CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C)),
        HasAdmissibleChoice act lab Y C := by
  obtain ⟨C, hC⟩ := hS.exists_isSliceMaxClique
  have inst := hS.isElementaryAbelian_closure hC.1.1 hC.1.2
  exact ⟨C, hC, inst, hS.hasAdmissibleChoice hC⟩

theorem exists_canonical_identification :
    ∃ (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) (ψ : sliceGroup lab Y ≃* CFSG.Monster.B.Fischer.J),
      (∀ (h : sliceGroup lab Y) (v w : Y), (w : V) = act (h : S) v →
        (ψ h : Equiv.Perm CFSG.Monster.B.Fischer.Y) (Φ v) = Φ w) ∧
      ∃ (x : V) (hx : x ∈ Y), Φ ⟨x, hx⟩ = CFSG.Monster.B.Fischer.o ∧
        (ψ ⟨lab x, lab_mem_sliceGroup hx⟩ : Equiv.Perm CFSG.Monster.B.Fischer.Y) = tPerm := by
  obtain ⟨C, hC⟩ := hS.exists_isSliceMaxClique
  have inst := hS.isElementaryAbelian_closure hC.1.1 hC.1.2
  obtain ⟨x, hx, η, θ, hη, hθ, φ, hφ, α, hα, Φ, hΦ⟩ := hS.hasAdmissibleChoice hC
  obtain ⟨ψ, hψ, -, hxT, -⟩ := hS.canonical_permutation_identification hC hx hη hθ hφ hα hΦ
  exact ⟨Φ, ψ, hψ, x, hx.1, (FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα).phi_base hΦ, hxT⟩

theorem exists_adjEquiv
    {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass) :
    ∃ Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL, ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y := by
  obtain ⟨Φ, ψ, hψ, x, hx, hxo, hxT⟩ := hS.exists_canonical_identification
  obtain ⟨-, -, -, -, Ψ, -, hΨ, -⟩ :=
    hS.exact_fixed_E6_adjoint_intertwiner ρ hρ hroot Φ ψ hψ hx hxo hxT
  exact ⟨Ψ, hΨ⟩

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
