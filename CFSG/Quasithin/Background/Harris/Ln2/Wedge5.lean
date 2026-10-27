module

public import CFSG.Quasithin.Background.Harris.Ln2.Wedge5Setup
public import CFSG.Quasithin.Background.Harris.Ln2.Wedge5Count
public import CFSG.Quasithin.Background.Harris.Ln2.AutRank5
public import CFSG.Quasithin.Background.JonesParshallCurtisModels
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.OneCompActions

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Ln2

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis CFSG.Quasithin.B42Ln Matrix

local notation "𝕎" => Fin 10 → ZMod 2

theorem wedgeRep_mul (a b : G5) (w : 𝕎) : wedgeRep (a * b) w = wedgeRep a (wedgeRep b w) := by
  rw [map_mul, Module.End.mul_apply]

theorem wedgeRep_inv_apply (a : G5) (w : 𝕎) : wedgeRep a⁻¹ (wedgeRep a w) = w := by
  rw [← wedgeRep_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem eq_wedgeRep_of_inner
    (M : 𝕎 ≃ₗ[ZMod 2] 𝕎) (m : G5)
    (hM : ∀ x w, M (wedgeRep x w) = wedgeRep (m * x * m⁻¹) (M w)) : ∀ w, M w = wedgeRep m w := by
  let f : Module.End (ZMod 2) 𝕎 := (wedgeRep m⁻¹).comp M.toLinearMap
  have hf : ∀ g w, f (wedgeRep g w) = wedgeRep g (f w) := by
    intro g w
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hM, ← wedgeRep_mul, ← wedgeRep_mul, show m⁻¹ * (m * g * m⁻¹) = g * m⁻¹ by group]
  rcases commutes_scalar wedgeRep wedge_simple Ugrp e01 e01_ne e01_mem_fixU
    (fun x hx => wedge_fix hx) f hf with h0 | h1
  · exfalso
    have : M e01 = 0 := by
      have := LinearMap.congr_fun h0 e01
      simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at this
      simpa [wedgeRep_inv_apply] using congrArg (wedgeRep m) this
    exact e01_ne (M.injective (by simpa using this))
  · intro w
    have := LinearMap.congr_fun h1 w
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.one_apply] at this
    simpa [wedgeRep_inv_apply] using congrArg (wedgeRep m) this

theorem wedgeRep_eT (i j : Fin 5) (h : i ≠ j) (w : 𝕎) :
    wedgeRep (eT i j h) w = wedgeMat (eTM i j) *ᵥ w := by
  rw [wedgeRep_apply', coe_eT]

theorem graphAut_eT (j : Fin 4) :
    graphAut (eT 0 j.succ (Fin.succ_ne_zero j).symm) = eT j.succ 0 (Fin.succ_ne_zero j) := by
  apply Subtype.ext
  change (((eT 0 j.succ (Fin.succ_ne_zero j).symm)⁻¹ : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ = _
  rw [inv_eq_of_mul_eq_one_right (eT_mul_self _ _ _), coe_eT, coe_eT]
  revert j
  decide

theorem not_intertwines_graph (M : 𝕎 ≃ₗ[ZMod 2] 𝕎) (m : G5)
    (hM : ∀ x w, M (wedgeRep x w) = wedgeRep (m * graphAut x * m⁻¹) (M w)) : False := by
  have key : ∀ w ∈ fixSet fun j => wedgeMat (eTM j.succ 0),
      M.symm (wedgeRep m w) ∈ fixSet fun j => wedgeMat (eTM 0 j.succ) := by
    intro w hw
    rw [mem_fixSet] at hw ⊢
    intro j
    apply M.injective
    have h1 := hM (eT 0 j.succ (Fin.succ_ne_zero j).symm) (M.symm (wedgeRep m w))
    rw [graphAut_eT, LinearEquiv.apply_symm_apply] at h1
    have h2 : wedgeRep (eT j.succ 0 (Fin.succ_ne_zero j)) w = w := by
      rw [wedgeRep_eT]
      exact hw j
    have h3 : wedgeRep (m * eT j.succ 0 (Fin.succ_ne_zero j) * m⁻¹) (wedgeRep m w) =
        wedgeRep m w := by
      rw [← wedgeRep_mul, inv_mul_cancel_right, wedgeRep_mul, h2]
    rw [h3] at h1
    rw [← wedgeRep_eT _ _ (Fin.succ_ne_zero j).symm, h1, LinearEquiv.apply_symm_apply]
  have hle := Finset.card_le_card_of_injOn (fun w => M.symm (wedgeRep m w)) key
    (fun a _ b _ hab => by
      have := M.symm.injective hab
      simpa [wedgeRep_inv_apply] using congrArg (wedgeRep m⁻¹) this)
  rw [card_fixSet_axis, card_fixSet_center] at hle
  omega

theorem mem_of_normalizes_wedge5
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {L Γ : Subgroup (GLV V)}
    (hn : ∀ γ ∈ Γ, ∀ l ∈ L, γ * l * γ⁻¹ ∈ L)
    {θ : ↥L ≃* CFSG.Quasithin.JonesParshall.Curtis.G5} {β : V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)}
    (h : ActsAs L θ CFSG.Quasithin.JonesParshall.wedgeRep β) : ∀ γ ∈ Γ, γ ∈ L := by
  intro γ hγ
  obtain ⟨M, σ, hMβ, hMσ⟩ := exists_intertwiner h γ (hn γ hγ) (fun l hl => by
    simpa using hn γ⁻¹ (inv_mem hγ) l hl)
  rcases aut5_inner_or_graph σ with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hM : ∀ x w, M (wedgeRep x w) = wedgeRep (m * x * m⁻¹) (M w) := fun x w => by
      rw [hMσ]
      exact congrArg (fun y => wedgeRep y (M w)) (by rw [hm]; rfl)
    have hMm := eq_wedgeRep_of_inner M m hM
    have hγl : γ = ((θ.symm m : ↥L) : GLV V) := by
      refine LinearEquiv.ext fun v => β.injective ?_
      rw [← hMβ, hMm, h, MulEquiv.apply_symm_apply]
    exact hγl ▸ (θ.symm m).2
  · exact (not_intertwines_graph M m fun x w => by
      rw [hMσ]
      exact congrArg (fun y => wedgeRep y (M w)) (by rw [hm]; rfl)).elim

end CFSG.Quasithin.G11.Harris.Ln2
