module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ExcFrames

section Transport

variable {C : Type*} [Group C]

theorem exists_weylFrame_of_conj {τ : Tag} {p : ℕ} {A A₀ : Subgroup C}
    (ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* C) (hι₀ : Function.Injective ι₀)
    (hrange : ι₀.range = A₀) {c : C} (hc : A = A₀.map (MulAut.conj c).toMonoidHom)
    (hframe : ∀ β : MulAut C, β ^ p = 1 → (∀ b ∈ A₀, β b ∈ A₀) →
      ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
        β (ι₀ (Multiplicative.ofAdd s)) =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p w s))) :
    ∃ ι : Multiplicative (Fin τ.rank → ZMod p) →* C, Function.Injective ι ∧ ι.range = A ∧
      ∀ α : MulAut C, α ^ p = 1 → (∀ a ∈ A, α a ∈ A) →
        ∃ w : WeylGroup τ, ∀ s : Fin τ.rank → ZMod p,
          α (ι (Multiplicative.ofAdd s)) =
            ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
  refine ⟨(MulAut.conj c).toMonoidHom.comp ι₀, (MulAut.conj c).injective.comp hι₀, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange, hc]
  · intro α hα hstab
    set β : MulAut C := MulAut.conj c⁻¹ * α * MulAut.conj c with hβ
    have hβapply : ∀ x, β x = c⁻¹ * α (c * x * c⁻¹) * c := by
      intro x
      rw [hβ]
      simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
    have hβp : β ^ p = 1 := by
      have hconj : β = (MulAut.conj c)⁻¹ * α * MulAut.conj c := by rw [hβ, ← map_inv]
      rw [hconj]
      have hpow : ((MulAut.conj c)⁻¹ * α * MulAut.conj c) ^ p =
          (MulAut.conj c)⁻¹ * α ^ p * MulAut.conj c := by
        simpa only [inv_inv] using conj_pow (a := (MulAut.conj c)⁻¹) (b := α) (i := p)
      rw [hpow, hα, mul_one, inv_mul_cancel]
    have hβstab : ∀ b ∈ A₀, β b ∈ A₀ := by
      intro b hb
      have h1 : c * b * c⁻¹ ∈ A := by
        rw [hc]
        exact ⟨b, hb, by show (MulAut.conj c) b = c * b * c⁻¹; rw [MulAut.conj_apply]⟩
      have h2 : α (c * b * c⁻¹) ∈ A := hstab _ h1
      rw [hc] at h2
      obtain ⟨b', hb', hb'eq⟩ := h2
      have hb'eq' : c * b' * c⁻¹ = α (c * b * c⁻¹) := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hb'eq
      have hβb : β b = b' := by
        rw [hβapply, ← hb'eq']
        group
      rw [hβb]
      exact hb'
    obtain ⟨w, hw⟩ := hframe β hβp hβstab
    refine ⟨w, fun s => ?_⟩
    have h3 : c⁻¹ * α (c * ι₀ (Multiplicative.ofAdd s) * c⁻¹) * c =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)) := by
      rw [← hβapply (ι₀ (Multiplicative.ofAdd s)), hw s]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    show α ((MulAut.conj c) (ι₀ (Multiplicative.ofAdd s))) =
      (MulAut.conj c) (ι₀ (Multiplicative.ofAdd (TableBExc.torusAct τ p w s)))
    rw [MulAut.conj_apply, MulAut.conj_apply, ← h3]
    group

end Transport

end ExcFrames

end CFSG.StandardType
