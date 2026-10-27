module

public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs

public section

namespace CFSG.StandardType.SympMinus

open CFSG.StandardType SpCoord Multiplicative TypeBDatum

variable {p m : ℕ} [NeZero p]

theorem fixed_of_vanish_signedSupportedAut (S : Finset (Fin m))
    {f : Fin m → Multiplicative (ZMod p)} (hf : ∀ i ∈ S, f i = 1) :
    ∀ τ ∈ signedSupportedAut m p S, τ f = f := by
  intro τ hτ
  unfold signedSupportedAut at hτ
  refine Subgroup.closure_induction (p := fun τ _ => τ f = f) ?_ ?_ ?_ ?_ hτ
  · rintro τ (⟨i, hi, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · rw [sgnAut_apply, hf i hi, inv_one]
      exact Function.update_eq_self_iff.mpr (hf i hi).symm
    · funext j
      rw [permAut_apply, Function.comp_apply]
      by_cases hj : j = a ∨ j = b
      · have h1 : (Equiv.swap a b)⁻¹ j ∈ S := by
          rcases hj with rfl | rfl
          · simp [Equiv.swap_apply_left, hb]
          · simp [Equiv.swap_apply_right, ha]
        have h2 : j ∈ S := by rcases hj with rfl | rfl <;> assumption
        rw [hf _ h1, hf _ h2]
      · rw [not_or] at hj
        simp [Equiv.swap_apply_of_ne_of_ne hj.1 hj.2]
  · exact rfl
  · intro τ₁ τ₂ _ _ h₁ h₂
    change τ₁ (τ₂ f) = f
    rw [h₂, h₁]
  · intro τ _ h
    calc τ⁻¹ f = τ⁻¹ (τ f) := by rw [h]
      _ = f := by rw [MulAut.inv_apply_self]

theorem fixed_of_const_permSupportedAut (S : Finset (Fin m))
    {g : Fin m → Multiplicative (ZMod p)} {c : Multiplicative (ZMod p)} (hg : ∀ i ∈ S, g i = c) :
    ∀ π ∈ permSupportedAut m p S, π g = g := by
  intro π hπ
  unfold permSupportedAut at hπ
  refine Subgroup.closure_induction (p := fun π _ => π g = g) ?_ ?_ ?_ ?_ hπ
  · rintro π ⟨a, ha, b, hb, hab, rfl⟩
    funext j
    rw [permAut_apply, Function.comp_apply]
    by_cases hj : j = a ∨ j = b
    · have h1 : (Equiv.swap a b)⁻¹ j ∈ S := by
        rcases hj with rfl | rfl
        · simp [Equiv.swap_apply_left, hb]
        · simp [Equiv.swap_apply_right, ha]
      have h2 : j ∈ S := by rcases hj with rfl | rfl <;> assumption
      rw [hg _ h1, hg _ h2]
    · rw [not_or] at hj
      simp [Equiv.swap_apply_of_ne_of_ne hj.1 hj.2]
  · exact rfl
  · intro τ₁ τ₂ _ _ h₁ h₂
    change τ₁ (τ₂ g) = g
    rw [h₂, h₁]
  · intro τ _ h
    calc τ⁻¹ g = τ⁻¹ (τ g) := by rw [h]
      _ = g := by rw [MulAut.inv_apply_self]

theorem fixed_of_twisted_twistedPermAut (S : Finset (Fin m)) {s : Fin m → ZMod p}
    (hs : ∀ i, s i * s i = 1) {f : Fin m → Multiplicative (ZMod p)} {a : ZMod p}
    (hf : ∀ i ∈ S, toAdd (f i) = s i * a) :
    ∀ τ ∈ twistedPermAut m p S s hs, τ f = f := by
  intro τ hτ
  obtain ⟨π, hπ, rfl⟩ := Subgroup.mem_map.mp hτ
  have hd : ∀ g, (diagAut s hs)⁻¹ g = diagAut s hs g := fun g => rfl
  have hdd : ∀ g, diagAut s hs (diagAut s hs g) = g := by
    intro g
    funext i
    simp [diagAut_apply, ← mul_assoc, hs i]
  have hconst : ∀ i ∈ S, (diagAut s hs f) i = ofAdd a := by
    intro i hi
    rw [diagAut_apply, hf i hi, ← mul_assoc, hs i, one_mul]
  have hfix := fixed_of_const_permSupportedAut S hconst π hπ
  change (diagAut s hs) (π ((diagAut s hs)⁻¹ f)) = f
  rw [hd, hfix, hdd]

end CFSG.StandardType.SympMinus

end
