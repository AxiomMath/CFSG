module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.ActionAbs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action Equiv

section

variable {X : Type*} [Group X] (L K U : Subgroup X) [L.Normal] [K.Normal] [U.Normal]
  (α : ↥L →* Alt5) (hα : Function.Surjective α) (hker : ∀ ℓ : ↥L, α ℓ = 1 ↔ (ℓ : X) ∈ K)
  (β : ↥U ≃* Multiplicative (evenWeight 5))
  (hβ : ∀ (ℓ : ↥L) (u u' : ↥U), (u' : X) = (ℓ : X) * (u : X) * (ℓ : X)⁻¹ →
    Multiplicative.toAdd (β u') = vact ((α ℓ : Alt5) : Perm (Fin 5)) (Multiplicative.toAdd (β u)))

include hβ in
theorem pi_compat_gen (x : X) (u u' : ↥U) (h : (u' : X) = x * u * x⁻¹) :
    Multiplicative.toAdd (β u') =
      vact (piFun L K α hα hker x) (Multiplicative.toAdd (β u)) := by
  have hu' : u' = MulAut.conjNormal x u := by
    apply Subtype.ext; rw [MulAut.conjNormal_apply]; exact h
  have hg : ∀ w, vact (piFun L K α hα hker x)⁻¹ (fX U β x w) = w := by
    apply rigid (fun w => vact (piFun L K α hα hker x)⁻¹ (fX U β x w))
    · intro w w'
      show vact _ (fX U β x (w + w')) = vact _ (fX U β x w) + vact _ (fX U β x w')
      rw [fX_add, vact_add]
    · intro w w' h
      apply fX_inj U β x
      have := congrArg (vact (piFun L K α hα hker x)) h
      simpa [← vact_mul, vact_one] using this
    · intro σ hσ w
      show vact _ (fX U β x (vact σ w)) = vact σ (vact _ (fX U β x w))
      obtain ⟨ℓ, hℓ⟩ := hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩
      have hℓσ : ((α ℓ : Alt5) : Perm (Fin 5)) = σ := by rw [hℓ]
      set u₀ := β.symm (Multiplicative.ofAdd w) with hu₀
      have hw : w = Multiplicative.toAdd (β u₀) := by simp [hu₀]
      have h1 : vact σ w = Multiplicative.toAdd (β (MulAut.conjNormal (ℓ : X) u₀)) := by
        rw [hβ ℓ u₀ _ (by rw [MulAut.conjNormal_apply]), hℓσ, ← hw]
      have h2 : MulAut.conjNormal x (MulAut.conjNormal (ℓ : X) u₀) =
          MulAut.conjNormal ((MulAut.conjNormal x ℓ : ↥L) : X) (MulAut.conjNormal x u₀) := by
        apply Subtype.ext
        simp only [MulAut.conjNormal_apply]
        group
      have h3 : fX U β x (vact σ w) =
          vact ((piFun L K α hα hker x) * σ * (piFun L K α hα hker x)⁻¹) (fX U β x w) := by
        rw [h1, fX_bU, h2]
        rw [hβ (MulAut.conjNormal x ℓ) (MulAut.conjNormal x u₀) _ rfl]
        rw [hw, fX_bU]
        congr 1
        rw [← psiHom_apply L K α hα hker x ℓ]
        rw [← hℓσ, ← piFun_spec]
      rw [h3, ← vact_mul, ← vact_mul]
      congr 1
      group
  have h5 := hg (Multiplicative.toAdd (β u))
  rw [fX_bU] at h5
  have h6 := congrArg (vact (piFun L K α hα hker x)) h5
  rw [← vact_mul, mul_inv_cancel, vact_one] at h6
  rw [hu']
  exact h6

include hα hker hβ in
theorem exists_pi_gen : ∃ π : X →* Perm (Fin 5),
    (∀ (x : X) (u u' : ↥U), (u' : X) = x * u * x⁻¹ →
      Multiplicative.toAdd (β u') = vact (π x) (Multiplicative.toAdd (β u))) ∧
    (∀ ℓ : ↥L, π (ℓ : X) = ((α ℓ : Alt5) : Perm (Fin 5))) :=
  ⟨piHom L K α hα hker, fun x u u' h => pi_compat_gen L K U α hα hker β hβ x u u' h,
    fun ℓ => piFun_alt L K α hα hker ℓ⟩

end

end CFSG.Quasithin.Vol2.Ch10.SecF
