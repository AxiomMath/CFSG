module

public import CFSG.Monster.GMS.AmalgamIso
public import CFSG.Monster.GMS.S4FamilyIso

public section

namespace CFSG.Monster.GMS

open CFSG.Monster.GMS.S4Family CFSG.Monster.GMS.S4Assembly

section Restrict

variable {X X' : Type*} [Group X] [Group X'] {f : X → X'} {H : Subgroup X} {H' : Subgroup X'}

theorem IsIsoOn.restrict (hf : IsIsoOn f H H') {H₁ : Subgroup X} {H₁' : Subgroup X'}
    (h₁ : H₁ ≤ H) (h₁' : H₁' ≤ H') (hiff : ∀ g ∈ H, f g ∈ H₁' ↔ g ∈ H₁) :
    IsIsoOn f H₁ H₁' where
  map_mem g hg := (hiff g (h₁ hg)).2 hg
  map_mul x hx y hy := hf.map_mul x (h₁ hx) y (h₁ hy)
  injOn x hx y hy hxy := hf.injOn (h₁ hx) (h₁ hy) hxy
  surjOn z hz := by
    obtain ⟨x, hx, rfl⟩ := hf.surjOn z (h₁' hz)
    exact ⟨x, (hiff x hx).1 hz, rfl⟩

theorem conj_eq_iff_of_isIsoOn (hf : IsIsoOn f H H') {g n m : X} (hg : g ∈ H) (hn : n ∈ H)
    (hm : m ∈ H) : f g * f n * (f g)⁻¹ = f m ↔ g * n * g⁻¹ = m := by
  rw [← iso_map_conj hf hg hn]
  exact ⟨fun e => hf.injOn (H.mul_mem (H.mul_mem hg hn) (H.inv_mem hg)) hm e, fun e => by rw [e]⟩

theorem fix_or_swap_iff_of_isIsoOn (hf : IsIsoOn f H H') {a y g : X} (ha : a ∈ H) (hy : y ∈ H)
    (hg : g ∈ H) :
    ((f g * f a * (f g)⁻¹ = f a ∧ f g * f y * (f g)⁻¹ = f y) ∨
      (f g * f a * (f g)⁻¹ = f y ∧ f g * f y * (f g)⁻¹ = f a)) ↔
    ((g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨ (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a)) := by
  rw [conj_eq_iff_of_isIsoOn hf hg ha ha, conj_eq_iff_of_isIsoOn hf hg hy hy,
    conj_eq_iff_of_isIsoOn hf hg ha hy, conj_eq_iff_of_isIsoOn hf hg hy ha]

end Restrict

section Amalgam

variable {V V' : Type*} {Γ : SimpleGraph V} {Γ' : SimpleGraph V'} {X X' : Type*} [Group X]
  [Group X'] [MulAction X V] [MulAction X' V'] {ι : Type*}

theorem symm_compat_of_isIsoOn {H₁ H₂ : Subgroup X} {H₁' H₂' : Subgroup X'} {f₁ f₂ : X → X'}
    (h₁ : IsIsoOn f₁ H₁ H₁') (h₂ : IsIsoOn f₂ H₂ H₂') (hc : ∀ g ∈ H₁ ⊓ H₂, f₁ g = f₂ g)
    (hback : ∀ g ∈ H₁, f₁ g ∈ H₂' → g ∈ H₂) (g' : X') (hg' : g' ∈ H₁') (hb' : g' ∈ H₂') :
    (((isoEquiv h₁).symm ⟨g', hg'⟩ : H₁) : X) = (((isoEquiv h₂).symm ⟨g', hb'⟩ : H₂) : X) := by
  set b := (isoEquiv h₁).symm ⟨g', hg'⟩ with hb
  set c := (isoEquiv h₂).symm ⟨g', hb'⟩ with hc'
  have e1 : f₁ (b : X) = g' := congrArg Subtype.val ((isoEquiv h₁).apply_symm_apply ⟨g', hg'⟩)
  have e2 : f₂ (c : X) = g' := congrArg Subtype.val ((isoEquiv h₂).apply_symm_apply ⟨g', hb'⟩)
  have hbH₂ : (b : X) ∈ H₂ := hback b b.2 (e1 ▸ hb')
  exact h₂.injOn hbH₂ c.2 (by rw [← hc _ ⟨b.2, hbH₂⟩, e1, e2])

end Amalgam

end CFSG.Monster.GMS
