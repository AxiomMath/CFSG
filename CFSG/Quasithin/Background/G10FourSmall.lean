module

public import CFSG.Quasithin.Background.G10FourPartner

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}

theorem g10Four_n_one_case_two (hyp : G101Hyp B Γ v₁ W X X₀) {U : Submodule (ZMod 2) V}
    (hUX : Invariant X U) (h1 : v₁ ∉ U) (h2 : ∃ u ∈ U, B v₁ u ≠ 0)
    (hU1 : Module.finrank (ZMod 2) U = 1) : commSpace X U = ⊥ := by
  obtain ⟨-, -, -, -, hker⟩ := hyp.counting U hUX h1 h2
  obtain ⟨z₀, hz₀, hB₀⟩ := G101Hyp.exists_one U h2
  have hbot : LinearMap.ker ((B v₁).domRestrict U) = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    omega
  rw [commSpace, Submodule.span_eq_bot]
  rintro w ⟨x, hx, u, hu, rfl⟩
  obtain ⟨hmem, hperp⟩ := hyp.center_mem U hUX hz₀ hB₀ hx
  have hker0 : (⟨x z₀ - z₀, hmem⟩ : U) ∈ LinearMap.ker ((B v₁).domRestrict U) := by
    rw [LinearMap.mem_ker]
    exact hperp
  rw [hbot, Submodule.mem_bot] at hker0
  have hc0 : x z₀ - z₀ = 0 := congrArg Subtype.val hker0
  rw [hyp.act_eq U hUX h1 hz₀ hB₀ hx hu, hc0]
  simp

theorem g10Four_n_one_case_one (hyp : G101Hyp B Γ v₁ W X X₀) {U : Submodule (ZMod 2) V}
    (hUΓ : Invariant Γ U) (h1 : v₁ ∉ U) (h2 : ∃ u ∈ U, B v₁ u ≠ 0)
    (hU1 : Module.finrank (ZMod 2) U = 1) (hdV : Module.finrank (ZMod 2) V = 2) : False := by
  have hUX : Invariant X U := fun x hx u hu => hUΓ x (hyp.X_le hx) u hu
  obtain ⟨hWU, -, -, -, -⟩ := hyp.counting U hUX h1 h2
  have hsup := hyp.sup_eq_top hUX h1 h2
  have hWspan : W = Submodule.span (ZMod 2) {v₁} := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hyp.mem_W
    · rw [finrank_span_singleton hyp.point]
      omega
  have hmove : ∀ γ ∈ Γ, γ v₁ - v₁ ∈ U := by
    intro γ hγ
    have hv : γ v₁ ∈ U ⊔ W := by
      rw [hsup]
      trivial
    obtain ⟨a, ha, w, hw, hav⟩ := Submodule.mem_sup.1 hv
    rw [hWspan, Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rcases g10Four_zmod_two_cases c with rfl | rfl
    · exfalso
      apply h1
      have : γ v₁ ∈ U := by
        rw [← hav, zero_smul, add_zero]
        exact ha
      have h3 := hUΓ γ⁻¹ (Γ.inv_mem hγ) _ this
      simpa using h3
    · rw [one_smul] at hav
      rw [← hav]
      simpa using ha
  let C : Subgroup (GLV V) := Γ ⊓ MulAction.stabilizer (GLV V) v₁
  have hodd : Odd (C.relIndex Γ) := by
    have := hyp.odd_index
    rwa [G101Hyp.stabilizer_eq_subgroupOf] at this
  have hfix : ∀ b ∈ Γ, b v₁ = v₁ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g₀, hg₀, hg₀ne⟩ := hcon
    have hdvd : C.relIndex Γ ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff']
      refine ⟨g₀⁻¹, Γ.inv_mem hg₀, fun b hb => ?_⟩
      by_cases hbC : b v₁ = v₁
      · exact Or.inr ⟨hb, hbC⟩
      · left
        refine ⟨Γ.mul_mem (Γ.inv_mem hg₀) hb, ?_⟩
        have hbne : b v₁ - v₁ ≠ 0 := fun h => hbC (sub_eq_zero.1 h)
        have hgne : g₀ v₁ - v₁ ≠ 0 := fun h => hg₀ne (sub_eq_zero.1 h)
        have heq := g10Four_eq_of_finrank_le_one U hU1.le (hmove b hb) (hmove g₀ hg₀) hbne hgne
        have hbg : b v₁ = g₀ v₁ := sub_left_injective heq
        show (g₀⁻¹ * b) v₁ = v₁
        rw [LinearEquiv.mul_apply, hbg]
        simp
    have hone : C.relIndex Γ = 1 := by
      have hodd' : Odd (C.relIndex Γ) := hodd
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd'
        exact absurd hodd' (by decide)
    have hle : Γ ≤ C := Subgroup.relIndex_eq_one.1 hone
    exact hg₀ne (hle hg₀).2
  have hle : Submodule.span (ZMod 2) (MulAction.orbit Γ v₁) ≤ Submodule.span (ZMod 2) {v₁} := by
    apply Submodule.span_mono
    rintro w ⟨γ, rfl⟩
    exact hfix γ γ.2
  rw [hyp.span_orbit] at hle
  have := Submodule.finrank_mono hle
  rw [finrank_top, finrank_span_singleton hyp.point] at this
  omega

end CFSG.Quasithin
