module

public import CFSG.Quasithin.Recognition.G112A2HatM22
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin.HatM22 CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def ActsAs (ψ : V ≃+ (Fin 6 → FieldFour)) (γ : V ≃ₗ[ZMod 2] V)
    (g : Matrix (Fin 6) (Fin 6) FieldFour) : Prop :=
  ∀ v, ψ (γ v) = g.mulVec (ψ v)

@[expose] def Semilinear (ψ : V ≃+ (Fin 6 → FieldFour)) (γ : V ≃ₗ[ZMod 2] V) : Prop :=
  ∀ (c : FieldFour) (v : V), ψ (γ (ψ.symm (c • ψ v))) = (c * c) • ψ (γ v)

@[expose] def G112Concl13Mod (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  Module.finrank (ZMod 2) V = 12 ∧ Nat.card Γ = 2661120 ∧
    ∃ ψ : V ≃+ (Fin 6 → FieldFour),
      (∀ g ∈ hatM22Γ₀, ∃ γ ∈ Γ, ActsAs ψ γ
        ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) ∧
      ∀ γ ∈ Γ, (∃ g ∈ hatM22Γ₀, ActsAs ψ γ
        ((g : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour)) ∨
        Semilinear ψ γ

theorem card_range_of_actsAs {ψ : V ≃+ (Fin 6 → FieldFour)} {γ : V ≃ₗ[ZMod 2] V}
    {g : Matrix (Fin 6) (Fin 6) FieldFour} (h : ActsAs ψ γ g) :
    Nat.card (LinearMap.range (γ.toLinearMap - LinearMap.id)) =
      Nat.card (LinearMap.range (Matrix.toLin' g - LinearMap.id)) := by
  apply Nat.card_congr
  refine (ψ.toEquiv.subtypeEquiv fun w => ?_)
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨ψ v, ?_⟩
    simp [Matrix.toLin'_apply, ← h v]
  · rintro ⟨x, hx⟩
    refine ⟨ψ.symm x, ψ.injective ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub,
      AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe] at hx ⊢
    rw [h, AddEquiv.apply_symm_apply, ← hx]
    simp [Matrix.toLin'_apply]

theorem finrank_ne_two_of_actsAs {ψ : V ≃+ (Fin 6 → FieldFour)} {γ : V ≃ₗ[ZMod 2] V}
    {g : ↥hatM22Γ₀} (h : ActsAs ψ γ (mat g)) :
    Module.finrank (ZMod 2) (LinearMap.range (γ.toLinearMap - LinearMap.id)) ≠ 2 := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := card_range_of_actsAs h
  rw [← FiniteField.pow_finrank_eq_natCard 2, h2, Module.natCard_eq_pow_finrank (K := FieldFour),
    natCard_eq] at hc
  have h4 : Module.finrank FieldFour (LinearMap.range (Matrix.toLin' (mat g) - LinearMap.id)) = 1 := by
    have h' : (4 : ℕ) ^ 1 = 4 ^ Module.finrank FieldFour
        (LinearMap.range (Matrix.toLin' (mat g) - LinearMap.id)) := by simpa using hc
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h').symm
  exact finrank_range_sub_ne_one g h4

theorem card_fix_le {t : (Fin 6 → FieldFour) → (Fin 6 → FieldFour)}
    (hadd : ∀ x y, t (x + y) = t x + t y) (hsl : ∀ (c : FieldFour) x, t (c • x) = (c * c) • t x) :
    Nat.card {x // t x = x} ≤ 2 ^ 6 := by
  have hsub : ∀ x y, t (x - y) = t x - t y := fun x y => by
    have := hadd (x - y) y
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  have hinj : Function.Injective (fun p : {x // t x = x} × {x // t x = x} =>
      (p.1 : Fin 6 → FieldFour) + ω • (p.2 : Fin 6 → FieldFour)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    simp only at h
    have h1 : a - a' = ω • (b' - b) := by
      rw [smul_sub]
      linear_combination (norm := module) h
    have h2 : t (a - a') = a - a' := by rw [hsub, ha, ha']
    rw [h1, hsl, hsub, hb, hb'] at h2
    have h3 : (ω * ω - ω) • (b' - b) = 0 := by
      rw [sub_smul, h2, sub_self]
    have hne : ω * ω - ω ≠ 0 := by decide
    have h4 : b' - b = 0 := (smul_eq_zero.mp h3).resolve_left hne
    have hbb : b = b' := (sub_eq_zero.mp h4).symm
    subst hbb
    have haa : a = a' := by
      have := h1
      rw [sub_self, smul_zero, sub_eq_zero] at this
      exact this
    subst haa
    rfl
  have hc := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_fun, natCard_eq, Nat.card_fin] at hc
  by_contra hlt
  push_neg at hlt
  have : (2 ^ 6 + 1) * (2 ^ 6 + 1) ≤ Nat.card {x // t x = x} * Nat.card {x // t x = x} :=
    Nat.mul_le_mul hlt hlt
  norm_num at this hc
  omega

theorem six_le_finrank_of_semilinear (hV : Module.finrank (ZMod 2) V = 12)
    {ψ : V ≃+ (Fin 6 → FieldFour)} {γ : V ≃ₗ[ZMod 2] V} (h : Semilinear ψ γ) (h2 : γ * γ = 1) :
    6 ≤ Module.finrank (ZMod 2) (LinearMap.range (γ.toLinearMap - LinearMap.id)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t : (Fin 6 → FieldFour) → (Fin 6 → FieldFour) := fun x => ψ (γ (ψ.symm x)) with ht
  have hadd : ∀ x y, t (x + y) = t x + t y := fun x y => by simp [ht]
  have hsl : ∀ (c : FieldFour) x, t (c • x) = (c * c) • t x := fun c x => by
    have := h c (ψ.symm x)
    simpa [ht] using this
  have hfix := card_fix_le hadd hsl
  have hker : Nat.card (LinearMap.ker (γ.toLinearMap - LinearMap.id)) = Nat.card {x // t x = x} := by
    apply Nat.card_congr
    refine ψ.toEquiv.subtypeEquiv fun v => ?_
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      sub_eq_zero, ht, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, AddEquiv.symm_apply_apply]
    exact ⟨fun hv => by rw [hv], fun hv => ψ.injective hv⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (γ.toLinearMap - LinearMap.id)
  rw [hV] at hrn
  have hk : Module.finrank (ZMod 2) (LinearMap.ker (γ.toLinearMap - LinearMap.id)) ≤ 6 := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 (LinearMap.ker (γ.toLinearMap - LinearMap.id))
    rw [hker] at h1
    have h2' : 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (γ.toLinearMap - LinearMap.id)) ≤ 2 ^ 6 :=
      h1 ▸ hfix
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2'
  omega

theorem finrank_ne_two_of_concl13Mod {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} (h13 : G112Concl13Mod Γ)
    {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ Γ) (h2 : γ * γ = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (γ.toLinearMap - LinearMap.id)) ≠ 2 := by
  obtain ⟨hV, -, ψ, -, hall⟩ := h13
  rcases hall γ hγ with ⟨g, hg, hact⟩ | hsl
  · exact finrank_ne_two_of_actsAs (g := ⟨g, hg⟩) hact
  · have := six_le_finrank_of_semilinear hV hsl h2
    omega

theorem g112ConclA2_concl13Mod (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V) (W : Submodule (ZMod 2) V)
    (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)) (hH : G111Hyp B Γ v₁ W X X₀) (h13 : G112Concl13Mod Γ) :
    ∀ t ∈ X, Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 →
      v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id) → (∀ v, B v (t v) = 0) →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  intro t ht hr
  exact absurd hr (finrank_ne_two_of_concl13Mod h13 (hH.X_le ht) (hH.X_sq t ht))

end CFSG.Quasithin.G112A2
