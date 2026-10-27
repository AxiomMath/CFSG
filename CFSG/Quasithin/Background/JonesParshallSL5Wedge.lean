module

public import CFSG.Quasithin.Background.JonesParshallWedgeH1

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Assembly.LowTwoRank

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def repOfEnd {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (μ : G →* AddMonoid.End V) : Representation (ZMod 2) G V where
  toFun g := (μ g : V →+ V).toZModLinearMap 2
  map_one' := LinearMap.ext fun v => by
    change μ 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun v => by
    change μ (g * h) v = μ g (μ h v)
    rw [map_mul]
    rfl

@[expose] def wedgeRep : Representation (ZMod 2) (SpecialLinearGroup (Fin 5) (ZMod 2))
    (Fin 10 → ZMod 2) :=
  repOfEnd (muW (ZMod 2))

theorem card_Z1A_wedge
    : Nat.card (Z1A (muW (ZMod 2))) = 1 * Nat.card (B1A (muW (ZMod 2))) := by
  rw [Z1A_eq_B1A_wedge, one_mul]

@[expose] def additiveWedge :
    Additive (Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2))) ≃+ ⋀[ZMod 2]^2 (Fin 5 → ZMod 2) where
  toFun x := Multiplicative.toAdd (Additive.toMul x)
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem SL5ExteriorTwo.intertwiner {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.SL5ExteriorTwo ρ) :
    ∃ (θ : Γ ≃* SpecialLinearGroup (Fin 5) (ZMod 2)) (β : W ≃+ (Fin 10 → ZMod 2)),
      ∀ γ w, β (ρ γ w) = muW (ZMod 2) (θ γ) (β w) := by
  obtain ⟨α, θ₀, β₀, hw⟩ := h
  set e := specialLinearGroupEquivStatedSL 5 (ZMod 2)
  have hcoe : ∀ y : ↥(StatedSL 5 (ZMod 2)), ((e.symm y : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) =
        ((y : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := fun y => by
    rw [← specialLinearGroupEquivStatedSL_coe 5 (ZMod 2) (e.symm y), MulEquiv.apply_symm_apply]
  have ha := Witness.ambient (D := FFModel.extSq (ZMod 2) 5) rfl rfl hw
  refine ⟨(θ₀.trans α).trans e.symm, ((β₀.trans (secEquivAmb _ rfl rfl).toAdditive).trans
    additiveWedge).trans (wedgeEquiv (ZMod 2)).toAddEquiv, fun γ w => ?_⟩
  have h1 := congrArg (fun x => (wedgeEquiv (ZMod 2)) (additiveWedge x)) (ha γ w)
  refine h1.trans ?_
  change (wedgeEquiv (ZMod 2)) (exteriorPower.map 2 (Matrix.toLin'
      ((((θ₀.trans α) γ : ↥(StatedSL 5 (ZMod 2))) : GL (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2))) _) =
    (wedgeEquiv (ZMod 2)) (exteriorPower.map 2 (Matrix.toLin'
      ((e.symm ((θ₀.trans α) γ) : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2))) ((wedgeEquiv (ZMod 2)).symm ((wedgeEquiv (ZMod 2)) _)))
  rw [hcoe, LinearEquiv.symm_apply_apply]
  rfl

theorem finrank_H1_SL5ExteriorTwo {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.SL5ExteriorTwo ρ) : Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  obtain ⟨θ, β, hβ⟩ := SL5ExteriorTwo.intertwiner h
  have : Finite Γ := Finite.of_equiv _ θ.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β.toEquiv.symm
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ card_Z1A_wedge, pow_zero]

end CFSG.Quasithin.JonesParshall
