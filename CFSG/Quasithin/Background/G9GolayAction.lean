module

public import CFSG.Quasithin.Background.G9GolayModels

public section

namespace CFSG.Quasithin.G11

theorem exists_golay_action {Model : Type} [Group Model] (small : Bool) (T : Equiv.Perm (Fin 24))
    {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (hΓ : ∀ g : Equiv.Perm (Fin 24), g ∈ Γ ↔
      ((∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
          permAct (T⁻¹ * g * T) w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode) ∧
        (small = true → (T⁻¹ * g * T) 0 = 0 ∧ (T⁻¹ * g * T) 1 = 1)))
    (φ : Model ≃* ↥Γ) :
    ∃ action : Model →* Equiv.Perm (Fin 24), Function.Injective action ∧
      (∀ m : Model, action m = T⁻¹ * (φ m : Equiv.Perm (Fin 24)) * T) ∧
      ∀ σ : Equiv.Perm (Fin 24), (∃ m : Model, action m = σ) ↔
        ((∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
            permAct σ w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode) ∧
          (small = true → σ 0 = 0 ∧ σ 1 = 1)) := by
  let action : Model →* Equiv.Perm (Fin 24) :=
    ((MulAut.conj T⁻¹).toMonoidHom).comp (Γ.subtype.comp φ.toMonoidHom)
  have haction : ∀ m : Model, action m = T⁻¹ * (φ m : Equiv.Perm (Fin 24)) * T := by
    intro m
    show (MulAut.conj T⁻¹) ((φ m : ↥Γ) : Equiv.Perm (Fin 24)) =
      T⁻¹ * (φ m : Equiv.Perm (Fin 24)) * T
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨action, ?_, haction, ?_⟩
  · intro a b hab
    have h1 : (MulAut.conj T⁻¹) ((φ a : ↥Γ) : Equiv.Perm (Fin 24)) =
        (MulAut.conj T⁻¹) ((φ b : ↥Γ) : Equiv.Perm (Fin 24)) := hab
    have h2 : ((φ a : ↥Γ) : Equiv.Perm (Fin 24)) =
        ((φ b : ↥Γ) : Equiv.Perm (Fin 24)) := (MulAut.conj T⁻¹).injective h1
    exact φ.injective (Subtype.ext h2)
  · intro σ
    constructor
    · rintro ⟨m, hm⟩
      have h := (hΓ ((φ m : ↥Γ) : Equiv.Perm (Fin 24))).1 (φ m).2
      rw [← haction m] at h
      rwa [hm] at h
    · intro hσ
      let γ : Equiv.Perm (Fin 24) := T * σ * T⁻¹
      have hγeq : T⁻¹ * γ * T = σ := by
        simp only [γ]
        group
      have hγ : γ ∈ Γ := by
        refine (hΓ γ).2 ?_
        rwa [hγeq]
      refine ⟨φ.symm ⟨γ, hγ⟩, ?_⟩
      rw [haction, MulEquiv.apply_symm_apply φ]
      exact hγeq

end CFSG.Quasithin.G11
