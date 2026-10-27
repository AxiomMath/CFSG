module

public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts

public section

namespace CFSG.Quasithin

namespace S143

open CFSG.QuasithinUnique

variable {W : Type*} [CommGroup W] [Finite W]

theorem card_le_two_of_invariant {q : W → ZMod 2} {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}
    (hS : OfourStruct X L₁ L₂ t)
    (hq : ∀ w, q w = 1 ↔ (w ∈ commV L₁ ∨ w ∈ commV L₂) ∧ w ≠ 1)
    {T' : Subgroup (MulAut W)} (hT : IsSylowTwoOf T' X)
    (F : Subgroup W) (hF : ∀ f ∈ F, q f = 0) (hinv : ∀ x ∈ T', ∀ f ∈ F, x f ∈ F) :
    Nat.card F ≤ 2 := by
  obtain ⟨s₁, s₂, τ, a₁, a₂, hSF⟩ := hS.exists_sylowFacts hT
  have hs₁T : s₁ ∈ T' := (hSF.sylow.s₁_mem_S).1
  have hs₁L : s₁ ∈ L₁ := hSF.sylow.s₁_mem_L
  have hfix₁ := hSF.sylow.fix₁
  have hF1 : ∀ f ∈ F, f ∈ commV L₁ → f = 1 := fun f hf hf1 => by
    by_contra hne
    have h1 := (hq f).mpr ⟨Or.inl hf1, hne⟩
    rw [hF f hf] at h1
    exact zero_ne_one h1
  have hF2 : ∀ f ∈ F, f ∈ commV L₂ → f = 1 := fun f hf hf2 => by
    by_contra hne
    have h1 := (hq f).mpr ⟨Or.inr hf2, hne⟩
    rw [hF f hf] at h1
    exact zero_ne_one h1
  have hC : ∀ f ∈ F, ∀ f₁ ∈ commV L₁, ∀ f₂ ∈ commV L₂, f = f₁ * f₂ → f₁ = 1 ∨ f₁ = a₁ := by
    intro f hf f₁ hf₁ f₂ hf₂ hfe
    have hs₁f₂ : s₁ f₂ = f₂ := hS.L₁_fix₂ hs₁L hf₂
    have hsf : s₁ f = s₁ f₁ * f₂ := by rw [hfe, map_mul, hs₁f₂]
    have hmem : s₁ f ∈ F := hinv s₁ hs₁T f hf
    have h1 : f₁⁻¹ * s₁ f₁ ∈ F := by
      have e : f⁻¹ * s₁ f = f₁⁻¹ * s₁ f₁ := by
        rw [hsf, hfe, mul_inv]
        calc f₁⁻¹ * f₂⁻¹ * (s₁ f₁ * f₂) = f₁⁻¹ * s₁ f₁ * (f₂⁻¹ * f₂) := by ac_rfl
          _ = f₁⁻¹ * s₁ f₁ := by rw [inv_mul_cancel, mul_one]
      rw [← e]
      exact F.mul_mem (F.inv_mem hf) hmem
    have h2 : f₁⁻¹ * s₁ f₁ ∈ commV L₁ :=
      (commV L₁).mul_mem ((commV L₁).inv_mem hf₁) (commV_stable L₁ hs₁L hf₁)
    have h3 := hF1 _ h1 h2
    have h4 : s₁ f₁ = f₁ := inv_mul_eq_one.mp h3 |>.symm
    exact (hfix₁ f₁ hf₁).mp h4
  have hD : ∀ f ∈ F, ∀ f' ∈ F, f ≠ 1 → f' ≠ 1 → f = f' := by
    have hone : ∀ f ∈ F, f ≠ 1 → ∀ f₁ ∈ commV L₁, ∀ f₂ ∈ commV L₂, f = f₁ * f₂ → f₁ = a₁ := by
      intro f hf hf1 f₁ hf₁ f₂ hf₂ hfe
      rcases hC f hf f₁ hf₁ f₂ hf₂ hfe with h1 | h1
      · exfalso
        apply hf1
        have : f = f₂ := by rw [hfe, h1, one_mul]
        rw [this]
        exact hF2 f₂ (this ▸ hf) hf₂
      · exact h1
    intro f hf f' hf' hf1 hf1'
    obtain ⟨f₁, hf₁, f₂, hf₂, hfe⟩ := hS.exists_decomp_W f
    obtain ⟨g₁, hg₁, g₂, hg₂, hge⟩ := hS.exists_decomp_W f'
    have hf₁a : f₁ = a₁ := hone f hf hf1 f₁ hf₁ f₂ hf₂ hfe
    have hg₁a : g₁ = a₁ := hone f' hf' hf1' g₁ hg₁ g₂ hg₂ hge
    have h1 : f⁻¹ * f' = f₂⁻¹ * g₂ := by
      rw [hfe, hge, hf₁a, hg₁a, mul_inv]
      calc a₁⁻¹ * f₂⁻¹ * (a₁ * g₂) = (a₁⁻¹ * a₁) * (f₂⁻¹ * g₂) := by ac_rfl
        _ = f₂⁻¹ * g₂ := by rw [inv_mul_cancel, one_mul]
    have h2 : f⁻¹ * f' ∈ F := F.mul_mem (F.inv_mem hf) hf'
    have h3 : f⁻¹ * f' ∈ commV L₂ := by
      rw [h1]
      exact (commV L₂).mul_mem ((commV L₂).inv_mem hf₂) hg₂
    exact inv_mul_eq_one.mp (hF2 _ h2 h3)
  by_contra hcon
  push Not at hcon
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card] at hcon
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcon
  have key : ∀ x y : F, x ≠ 1 → y ≠ 1 → x = y := fun x y hx hy =>
    Subtype.ext (hD x x.2 y y.2 (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h)))
  by_cases ha : a = 1
  · exact hbc (key b c (fun hb => hab (ha.trans hb.symm)) (fun hc => hac (ha.trans hc.symm)))
  · by_cases hb : b = 1
    · exact hac (key a c ha (fun hc => hbc (hb.trans hc.symm)))
    · exact hab (key a b ha hb)

end S143

end CFSG.Quasithin
