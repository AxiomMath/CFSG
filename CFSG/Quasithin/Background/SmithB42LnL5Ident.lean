module

public import CFSG.Quasithin.Background.SmithB42LnL5Dim
public import CFSG.Quasithin.Background.SmithB51LnReal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis Matrix
open CFSG.Assembly.LowTwoRank

local notation "𝕄" => Matrix (Fin 5) (Fin 5) (ZMod 2)

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

@[expose] noncomputable def piW (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (κ : G5 ≃* G5) :
    ↥(StatedSL 5 (ZMod 2)) →* ↥L :=
  (phiOf e).symm.toMonoidHom.comp (κ.symm.toMonoidHom.comp E5.symm.toMonoidHom)

theorem piW_bijective (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (κ : G5 ≃* G5) :
    Function.Bijective (piW e κ) :=
  ((E5.symm.trans κ.symm).trans (phiOf e).symm).bijective

theorem coe_piW (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) (κ : G5 ≃* G5)
    (γ : ↥(StatedSL 5 (ZMod 2))) :
    ((piW e κ γ : ↥L) : MulAut V) = fL e (κ.symm (E5.symm γ)) := rfl

section Rep

variable [Module (ZMod 2) (Additive V)]

theorem not_trivial (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2)))
    (h : ∀ g w, repOf (phiOf e) g w = w) : False := by
  have h1 : ∀ g : G5, fL e g = 1 := fun g => MulEquiv.ext fun v => by
    have := h g (Additive.ofMul v)
    rw [repOf_apply] at this
    exact Additive.ofMul.injective this
  apply eT01_mul_eT10_ne
  apply fL_injective e
  rw [map_mul, map_mul, h1, h1]

@[expose] noncomputable def coordHom {k : ℕ} (β : Additive V ≃ₗ[ZMod 2] (Fin k → ZMod 2)) :
    ↥(⊤ : Subgroup V) →* Multiplicative (Fin k → ZMod 2) where
  toFun v := Multiplicative.ofAdd (β (Additive.ofMul (v : V)))
  map_one' := by simp
  map_mul' v w := by simp [ofMul_mul, ofAdd_add]

theorem coordHom_surjective {k : ℕ} (β : Additive V ≃ₗ[ZMod 2] (Fin k → ZMod 2)) :
    Function.Surjective (coordHom β) := by
  intro y
  refine ⟨⟨Additive.toMul (β.symm (Multiplicative.toAdd y)), Subgroup.mem_top _⟩, ?_⟩
  show Multiplicative.ofAdd (β (Additive.ofMul (Additive.toMul _))) = y
  rw [ofMul_toMul, LinearEquiv.apply_symm_apply, ofAdd_toAdd]

theorem coordHom_eq_one {k : ℕ} (β : Additive V ≃ₗ[ZMod 2] (Fin k → ZMod 2))
    (u : ↥(⊤ : Subgroup V)) : coordHom β u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := by
  rw [Subgroup.mem_bot]
  constructor
  · intro h
    have h1 : β (Additive.ofMul (u : V)) = 0 := congrArg Multiplicative.toAdd h
    have h2 : Additive.ofMul (u : V) = 0 := by
      rw [← map_zero β] at h1
      exact β.injective h1
    exact Additive.ofMul.injective h2
  · intro h
    show Multiplicative.ofAdd (β (Additive.ofMul (u : V))) = 1
    rw [h, ofMul_one, map_zero, ofAdd_zero]

theorem binaryNaturalSL_of_nat (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {κ : G5 ≃* G5}
    {β : Additive V ≃ₗ[ZMod 2] (Fin 5 → ZMod 2)}
    (hβ : ∀ g w, β (repOf (phiOf e) g w) = natRep (κ g) (β w)) :
    BinaryNaturalSL L ⊤ ⊥ 5 1 := by
  have hact : ∀ γ : ↥(StatedSL 5 (ZMod 2)), natAct (StatedSL 5 (ZMod 2)) γ 1 = 1 := by
    intro γ
    show Multiplicative.ofAdd (_ *ᵥ Multiplicative.toAdd (1 : Multiplicative _)) = 1
    rw [toAdd_one, mulVec_zero]
    rfl
  have hequiv : ∀ (γ : ↥(StatedSL 5 (ZMod 2))) (u : ↥(⊤ : Subgroup V))
      (hu : ((piW e κ γ : ↥L) : MulAut V) (u : V) ∈ (⊤ : Subgroup V)),
      coordHom β ⟨((piW e κ γ : ↥L) : MulAut V) (u : V), hu⟩ =
        natAct (StatedSL 5 (ZMod 2)) γ (coordHom β u) := by
    intro γ u hu
    show Multiplicative.ofAdd (β (Additive.ofMul (((piW e κ γ : ↥L) : MulAut V) (u : V)))) =
      Multiplicative.ofAdd (B5.Ln.mat γ *ᵥ Multiplicative.toAdd
        (Multiplicative.ofAdd (β (Additive.ofMul (u : V)))))
    rw [toAdd_ofAdd]
    congr 1
    have h1 := hβ (κ.symm (E5.symm γ)) (Additive.ofMul (u : V))
    rw [MulEquiv.apply_symm_apply, natRep_apply, coe_E5_symm, repOf_apply, ← fL_apply,
      ← coe_piW] at h1
    exact h1
  refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, piW e κ, ?_⟩
  exact B5.Ln.realizesVia_of_coord (D := FFModel.nat (StatedSL 5 (ZMod 2))) rfl rfl
    hact (piW_bijective e κ).2 bot_le (fun _ _ _ => Subgroup.mem_top _)
    (fun h z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one]) (coordHom β)
    (coordHom_surjective β) (coordHom_eq_one β) hequiv

@[expose] noncomputable def wedgeHom (β : Additive V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)) :
    ↥(⊤ : Subgroup V) →* Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) where
  toFun v := Multiplicative.ofAdd ((wedgeEquiv (ZMod 2)).symm (β (Additive.ofMul (v : V))))
  map_one' := by simp
  map_mul' v w := by simp [ofMul_mul, ofAdd_add]

theorem realizesVia_extSq_of_wedge (e : ↥L ≃* ↥(StatedSL 5 (ZMod 2))) {κ : G5 ≃* G5}
    {β : Additive V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)}
    (hβ : ∀ g w, β (repOf (phiOf e) g w) = wedgeRep (κ g) (β w)) :
    (FFModel.extSq (ZMod 2) 5).RealizesVia L ⊤ ⊥ (piW e κ) := by
  have hact : ∀ γ : ↥(StatedSL 5 (ZMod 2)), extSqAct (ZMod 2) 5 γ 1 = 1 := by
    intro γ
    show Multiplicative.ofAdd (exteriorPower.map 2 _ (Multiplicative.toAdd 1)) = 1
    rw [toAdd_one, map_zero]
    rfl
  have hsurj : Function.Surjective (wedgeHom β) := by
    intro y
    refine ⟨⟨Additive.toMul (β.symm (wedgeEquiv (ZMod 2) (Multiplicative.toAdd y))),
      Subgroup.mem_top _⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    show (wedgeEquiv (ZMod 2)).symm (β (Additive.ofMul (Additive.toMul _))) = _
    simp
  have hker : ∀ u : ↥(⊤ : Subgroup V), wedgeHom β u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := by
    intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : (wedgeEquiv (ZMod 2)).symm (β (Additive.ofMul (u : V))) = 0 :=
        congrArg Multiplicative.toAdd h
      have h2 : β (Additive.ofMul (u : V)) = 0 := by
        have := congrArg (wedgeEquiv (ZMod 2)) h1
        rwa [LinearEquiv.apply_symm_apply, map_zero] at this
      have h3 : Additive.ofMul (u : V) = 0 := by
        rw [← map_zero β] at h2
        exact β.injective h2
      exact Additive.ofMul.injective h3
    · intro h
      show Multiplicative.ofAdd ((wedgeEquiv (ZMod 2)).symm (β (Additive.ofMul (u : V)))) = 1
      rw [h, ofMul_one, map_zero, map_zero, ofAdd_zero]
  have hequiv : ∀ (γ : ↥(StatedSL 5 (ZMod 2))) (u : ↥(⊤ : Subgroup V))
      (hu : ((piW e κ γ : ↥L) : MulAut V) (u : V) ∈ (⊤ : Subgroup V)),
      wedgeHom β ⟨((piW e κ γ : ↥L) : MulAut V) (u : V), hu⟩ =
        extSqAct (ZMod 2) 5 γ (wedgeHom β u) := by
    intro γ u hu
    show Multiplicative.ofAdd ((wedgeEquiv (ZMod 2)).symm (β (Additive.ofMul
      (((piW e κ γ : ↥L) : MulAut V) (u : V))))) =
      Multiplicative.ofAdd (exteriorPower.map 2 (Matrix.toLin' (B5.Ln.mat γ))
        (Multiplicative.toAdd (Multiplicative.ofAdd ((wedgeEquiv (ZMod 2)).symm
          (β (Additive.ofMul (u : V)))))))
    rw [toAdd_ofAdd]
    congr 1
    apply (wedgeEquiv (ZMod 2)).injective
    rw [LinearEquiv.apply_symm_apply, wedgeEquiv_apply, wedgeCoord_map, ← wedgeEquiv_apply,
      LinearEquiv.apply_symm_apply]
    have h1 := hβ (κ.symm (E5.symm γ)) (Additive.ofMul (u : V))
    rw [MulEquiv.apply_symm_apply, wedgeRep_apply', coe_E5_symm, repOf_apply, ← fL_apply,
      ← coe_piW] at h1
    exact h1
  exact B5.Ln.realizesVia_of_coord (D := FFModel.extSq (ZMod 2) 5) rfl rfl
    hact (piW_bijective e κ).2 bot_le (fun _ _ _ => Subgroup.mem_top _)
    (fun h z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one]) (wedgeHom β) hsurj
    hker hequiv

end Rep

end CFSG.Quasithin.B42Ln
