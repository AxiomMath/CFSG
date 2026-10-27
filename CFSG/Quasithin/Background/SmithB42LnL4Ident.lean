module

public import CFSG.Quasithin.Background.SmithB42LnL4Dim
public import CFSG.Quasithin.Background.SmithB42LnL5Ident

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall Matrix CFSG.Assembly.LowTwoRank

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

@[expose] noncomputable def piL4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (κ : G4 ≃* G4) :
    ↥(StatedSL 4 (ZMod 2)) →* ↥L :=
  (phiOf4 e).symm.toMonoidHom.comp (κ.symm.toMonoidHom.comp E4.symm.toMonoidHom)

theorem piL4_bijective (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (κ : G4 ≃* G4) :
    Function.Bijective (piL4 e κ) :=
  ((E4.symm.trans κ.symm).trans (phiOf4 e).symm).bijective

theorem coe_piL4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) (κ : G4 ≃* G4)
    (γ : ↥(StatedSL 4 (ZMod 2))) :
    ((piL4 e κ γ : ↥L) : MulAut V) = fL4 e (κ.symm (E4.symm γ)) := rfl

section Rep

variable [Module (ZMod 2) (Additive V)]

theorem binaryNaturalSL_of_nat4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))) {κ : G4 ≃* G4}
    {β : Additive V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)}
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = natRep4 (κ g) (β w)) :
    BinaryNaturalSL L ⊤ ⊥ 4 1 := by
  have hact : ∀ γ : ↥(StatedSL 4 (ZMod 2)), natAct (StatedSL 4 (ZMod 2)) γ 1 = 1 := by
    intro γ
    show Multiplicative.ofAdd (_ *ᵥ Multiplicative.toAdd (1 : Multiplicative _)) = 1
    rw [toAdd_one, mulVec_zero]
    rfl
  have hequiv : ∀ (γ : ↥(StatedSL 4 (ZMod 2))) (u : ↥(⊤ : Subgroup V))
      (hu : ((piL4 e κ γ : ↥L) : MulAut V) (u : V) ∈ (⊤ : Subgroup V)),
      coordHom β ⟨((piL4 e κ γ : ↥L) : MulAut V) (u : V), hu⟩ =
        natAct (StatedSL 4 (ZMod 2)) γ (coordHom β u) := by
    intro γ u hu
    show Multiplicative.ofAdd (β (Additive.ofMul (((piL4 e κ γ : ↥L) : MulAut V) (u : V)))) =
      Multiplicative.ofAdd (B5.Ln.mat γ *ᵥ Multiplicative.toAdd
        (Multiplicative.ofAdd (β (Additive.ofMul (u : V)))))
    rw [toAdd_ofAdd]
    congr 1
    have h1 := hβ (κ.symm (E4.symm γ)) (Additive.ofMul (u : V))
    rw [MulEquiv.apply_symm_apply, natRep4_apply, coe_E4_symm, repOf4_apply, ← fL4_apply,
      ← coe_piL4] at h1
    exact h1
  refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, piL4 e κ, ?_⟩
  exact B5.Ln.realizesVia_of_coord (D := FFModel.nat (StatedSL 4 (ZMod 2))) rfl rfl
    hact (piL4_bijective e κ).2 bot_le (fun _ _ _ => Subgroup.mem_top _)
    (fun h z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one]) (coordHom β)
    (coordHom_surjective β) (coordHom_eq_one β) hequiv

@[expose] noncomputable def wedgeHom4 (β : Additive V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :
    ↥(⊤ : Subgroup V) →* Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) where
  toFun v := Multiplicative.ofAdd ((wedgeEquiv4 (ZMod 2)).symm (β (Additive.ofMul (v : V))))
  map_one' := by simp
  map_mul' v w := by simp [ofMul_mul, ofAdd_add]

theorem realizesVia_extSq_of_wedge4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    {β : Additive V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = wedgeRep4' g (β w)) :
    (FFModel.extSq (ZMod 2) 4).RealizesVia L ⊤ ⊥ (piL4 e (MulEquiv.refl _)) := by
  have hact : ∀ γ : ↥(StatedSL 4 (ZMod 2)), extSqAct (ZMod 2) 4 γ 1 = 1 := by
    intro γ
    show Multiplicative.ofAdd (exteriorPower.map 2 _ (Multiplicative.toAdd 1)) = 1
    rw [toAdd_one, map_zero]
    rfl
  have hsurj : Function.Surjective (wedgeHom4 β) := by
    intro y
    refine ⟨⟨Additive.toMul (β.symm (wedgeEquiv4 (ZMod 2) (Multiplicative.toAdd y))),
      Subgroup.mem_top _⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    show (wedgeEquiv4 (ZMod 2)).symm (β (Additive.ofMul (Additive.toMul _))) = _
    simp
  have hker : ∀ u : ↥(⊤ : Subgroup V), wedgeHom4 β u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V) := by
    intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : (wedgeEquiv4 (ZMod 2)).symm (β (Additive.ofMul (u : V))) = 0 :=
        congrArg Multiplicative.toAdd h
      have h2 : β (Additive.ofMul (u : V)) = 0 := by
        have := congrArg (wedgeEquiv4 (ZMod 2)) h1
        rwa [LinearEquiv.apply_symm_apply, map_zero] at this
      have h3 : Additive.ofMul (u : V) = 0 := by
        rw [← map_zero β] at h2
        exact β.injective h2
      exact Additive.ofMul.injective h3
    · intro h
      show Multiplicative.ofAdd ((wedgeEquiv4 (ZMod 2)).symm (β (Additive.ofMul (u : V)))) = 1
      rw [h, ofMul_one, map_zero, map_zero, ofAdd_zero]
  have hequiv : ∀ (γ : ↥(StatedSL 4 (ZMod 2))) (u : ↥(⊤ : Subgroup V))
      (hu : ((piL4 e (MulEquiv.refl _) γ : ↥L) : MulAut V) (u : V) ∈ (⊤ : Subgroup V)),
      wedgeHom4 β ⟨((piL4 e (MulEquiv.refl _) γ : ↥L) : MulAut V) (u : V), hu⟩ =
        extSqAct (ZMod 2) 4 γ (wedgeHom4 β u) := by
    intro γ u hu
    show Multiplicative.ofAdd ((wedgeEquiv4 (ZMod 2)).symm (β (Additive.ofMul
      (((piL4 e (MulEquiv.refl _) γ : ↥L) : MulAut V) (u : V))))) =
      Multiplicative.ofAdd (exteriorPower.map 2 (Matrix.toLin' (B5.Ln.mat γ))
        (Multiplicative.toAdd (Multiplicative.ofAdd ((wedgeEquiv4 (ZMod 2)).symm
          (β (Additive.ofMul (u : V)))))))
    rw [toAdd_ofAdd]
    congr 1
    apply (wedgeEquiv4 (ZMod 2)).injective
    rw [LinearEquiv.apply_symm_apply, wedgeEquiv4_apply, wedgeCoord_map4, ← wedgeEquiv4_apply,
      LinearEquiv.apply_symm_apply]
    have h1 := hβ (E4.symm γ) (Additive.ofMul (u : V))
    rw [wedgeRep4'_apply, coe_E4_symm, repOf4_apply, ← fL4_apply] at h1
    exact h1
  exact B5.Ln.realizesVia_of_coord (D := FFModel.extSq (ZMod 2) 4) rfl rfl
    hact (piL4_bijective e _).2 bot_le (fun _ _ _ => Subgroup.mem_top _)
    (fun h z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one]) (wedgeHom4 β) hsurj
    hker hequiv

theorem slExteriorTwo_of_wedge4 (e : ↥L ≃* ↥(StatedSL 4 (ZMod 2)))
    {β : Additive V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = wedgeRep4' g (β w)) : SLExteriorTwo L ⊤ ⊥ 4 :=
  ⟨_, realizesVia_extSq_of_wedge4 e hβ⟩

end Rep

end CFSG.Quasithin.B42Ln
