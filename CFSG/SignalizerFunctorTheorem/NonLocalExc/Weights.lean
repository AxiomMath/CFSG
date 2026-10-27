module

public import CFSG.SignalizerFunctorTheorem.NonLocal.AbelianLift

public section

open Module Module.End CFSG.SignalizerFunctorTheorem.NonLocal
open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

variable {F W X Γ : Type*} [Field F] [AddCommGroup W] [Module F W] [Group X] [Group Γ]

@[expose] def conjV (φ : Γ →* X) (V : Subgroup X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g : Γ) (v : V) : V :=
  ⟨(φ g)⁻¹ * v * φ g, by simpa [map_inv] using hnorm g⁻¹ v v.2⟩

theorem coe_conjV (φ : Γ →* X) (V : Subgroup X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g : Γ) (v : V) :
    ((conjV φ V hnorm g v : V) : X) = (φ g)⁻¹ * v * φ g := rfl

theorem conjV_mul (φ : Γ →* X) (V : Subgroup X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g₁ g₂ : Γ) (v : V) :
    conjV φ V hnorm (g₁ * g₂) v = conjV φ V hnorm g₂ (conjV φ V hnorm g₁ v) :=
  Subtype.ext (by simp [coe_conjV, mul_assoc])

theorem conjV_one (φ : Γ →* X) (V : Subgroup X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (v : V) :
    conjV φ V hnorm 1 v = v :=
  Subtype.ext (by simp [coe_conjV])

theorem isWeight_conj {ρ : X →* End F W} {V : Subgroup X} {χ : V → F} (hχ : IsWeight ρ V χ)
    (φ : Γ →* X) (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g : Γ) :
    IsWeight ρ V (fun v => χ (conjV φ V hnorm g v)) := by
  obtain ⟨w, hw0, hw⟩ := hχ
  refine ⟨ρ (φ g) w, ?_, fun v => ?_⟩
  · intro h
    apply hw0
    have h1 : ρ ((φ g)⁻¹) (ρ (φ g) w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1, h, map_zero]
  · have h1 : ρ (v : X) * ρ (φ g) = ρ (φ g) * ρ ((conjV φ V hnorm g v : V) : X) := by
      rw [← map_mul, ← map_mul]
      congr 1
      simp [coe_conjV, mul_assoc]
    rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hw (conjV φ V hnorm g v), map_smul]

abbrev Wt (ρ : X →* End F W) (V : Subgroup X) : Type _ := {χ : V → F // IsWeight ρ V χ}

@[expose] def wtMap (ρ : X →* End F W) (V : Subgroup X) (φ : Γ →* X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g : Γ) (χ : Wt ρ V) : Wt ρ V :=
  ⟨fun v => χ.1 (conjV φ V hnorm g v), isWeight_conj χ.2 φ hnorm g⟩

theorem wtMap_apply (ρ : X →* End F W) (V : Subgroup X) (φ : Γ →* X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g : Γ) (χ : Wt ρ V) (v : V) :
    (wtMap ρ V φ hnorm g χ).1 v = χ.1 (conjV φ V hnorm g v) := rfl

theorem wtMap_one (ρ : X →* End F W) (V : Subgroup X) (φ : Γ →* X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (χ : Wt ρ V) :
    wtMap ρ V φ hnorm 1 χ = χ :=
  Subtype.ext (funext fun v => by rw [wtMap_apply, conjV_one])

theorem wtMap_mul (ρ : X →* End F W) (V : Subgroup X) (φ : Γ →* X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g₁ g₂ : Γ) (χ : Wt ρ V) :
    wtMap ρ V φ hnorm (g₁ * g₂) χ =
      wtMap ρ V φ hnorm g₁ (wtMap ρ V φ hnorm g₂ χ) :=
  Subtype.ext (funext fun v => by
    rw [wtMap_apply, wtMap_apply, wtMap_apply, conjV_mul])

@[expose] def weightAction (ρ : X →* End F W) (V : Subgroup X) (φ : Γ →* X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) : Γ →* Equiv.Perm (Wt ρ V) where
  toFun g :=
    { toFun := wtMap ρ V φ hnorm g
      invFun := wtMap ρ V φ hnorm g⁻¹
      left_inv := fun χ => by
        rw [← wtMap_mul, inv_mul_cancel, wtMap_one]
      right_inv := fun χ => by
        rw [← wtMap_mul, mul_inv_cancel, wtMap_one] }
  map_one' := Equiv.ext fun χ => wtMap_one ρ V φ hnorm χ
  map_mul' g₁ g₂ := Equiv.ext fun χ => wtMap_mul ρ V φ hnorm g₁ g₂ χ

theorem weightAction_apply (ρ : X →* End F W) (V : Subgroup X) (φ : Γ →* X)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g : Γ) (χ : Wt ρ V) (v : V) :
    ((weightAction ρ V φ hnorm g χ : Wt ρ V).1 v) = χ.1 (conjV φ V hnorm g v) := rfl

variable [IsAlgClosed F] [FiniteDimensional F W]

theorem centralizes_of_weightAction_eq_one (ρ : X →* End F W) (hρ : Function.Injective ρ)
    (V : Subgroup X) [Finite V] (hV : IsMulCommutative V) (hinv : (Nat.card V : F) ≠ 0)
    (φ : Γ →* X) (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V) (g : Γ)
    (hg : weightAction ρ V φ hnorm g = 1) : ∀ v ∈ V, φ g * v * (φ g)⁻¹ = v := by
  intro v hv
  set a : V := ⟨v, hv⟩ with ha
  have hfix : ∀ (χ : V → F), IsWeight ρ V χ → ∀ u : V, χ (conjV φ V hnorm g u) = χ u := by
    intro χ hχ u
    have := congrArg (fun f : Equiv.Perm (Wt ρ V) => (f ⟨χ, hχ⟩).1 u) hg
    simpa [weightAction_apply] using this
  have hc : ρ (φ g * v * (φ g)⁻¹ * v⁻¹) = (1 : F) • (1 : End F W) := by
    refine eq_smul_one_of_weights ρ V hV hinv _ 1 (fun χ hχ w hw => ?_)
    have hv1 : ρ (v⁻¹) w = (χ a)⁻¹ • w := by
      have h1 : ρ (((a⁻¹ : V)) : X) w = χ a⁻¹ • w := hw a⁻¹
      rw [hχ.inv a] at h1
      simpa using h1
    have hw' : ∀ u : V, ρ (u : X) (ρ ((φ g)⁻¹) w) = χ u • ρ ((φ g)⁻¹) w := by
      intro u
      have hmem : φ g * (u : X) * (φ g)⁻¹ ∈ V := hnorm g u u.2
      have h1 : ρ (u : X) * ρ ((φ g)⁻¹) = ρ ((φ g)⁻¹) * ρ (φ g * (u : X) * (φ g)⁻¹) := by
        rw [← map_mul, ← map_mul]
        congr 1
        simp [mul_assoc]
      have h2 := hw ⟨φ g * u * (φ g)⁻¹, hmem⟩
      have hfix' := hfix χ hχ ⟨φ g * u * (φ g)⁻¹, hmem⟩
      have h4 : conjV φ V hnorm g ⟨φ g * u * (φ g)⁻¹, hmem⟩ = u :=
        Subtype.ext (by simp [coe_conjV, mul_assoc])
      rw [h4] at hfix'
      rw [← Module.End.mul_apply, h1, Module.End.mul_apply, h2, map_smul, hfix']
    have hvg : ρ (v : X) (ρ ((φ g)⁻¹) w) = χ a • ρ ((φ g)⁻¹) w := hw' a
    have hne : χ a ≠ 0 := hχ.ne_zero a
    calc ρ (φ g * v * (φ g)⁻¹ * v⁻¹) w
        = ρ (φ g) (ρ v (ρ ((φ g)⁻¹) (ρ (v⁻¹) w))) := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ρ (φ g) (ρ v (ρ ((φ g)⁻¹) ((χ a)⁻¹ • w))) := by rw [hv1]
      _ = ρ (φ g) ((χ a)⁻¹ • ρ v (ρ ((φ g)⁻¹) w)) := by rw [map_smul, map_smul]
      _ = ρ (φ g) ((χ a)⁻¹ • (χ a • ρ ((φ g)⁻¹) w)) := by rw [hvg]
      _ = ρ (φ g) (ρ ((φ g)⁻¹) w) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (1 : F) • w := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
            one_smul]
  rw [one_smul] at hc
  have h1 : φ g * v * (φ g)⁻¹ * v⁻¹ = 1 := hρ (by rw [hc, map_one])
  exact mul_inv_eq_one.mp h1

theorem card_dvd_factorial_of_faithful (ρ : X →* End F W) (hρ : Function.Injective ρ)
    (V : Subgroup X) [Finite V] (hV : IsMulCommutative V) (hinv : (Nat.card V : F) ≠ 0)
    (φ : Γ →* X) (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V)
    (hfaith : ∀ g : Γ, (∀ v ∈ V, φ g * v * (φ g)⁻¹ = v) → g = 1) (R : Subgroup Γ) :
    Nat.card R ∣ (finrank F W).factorial := by
  classical
  obtain ⟨hfin, hcard⟩ := finite_card_weights ρ V hV
  have := Fintype.ofFinite (Wt ρ V)
  have hinj : Function.Injective (weightAction ρ V φ hnorm) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact hfaith g (centralizes_of_weightAction_eq_one ρ hρ V hV hinv φ hnorm g hg)
  have hRinj : Function.Injective ((weightAction ρ V φ hnorm).comp R.subtype) :=
    hinj.comp R.subtype_injective
  have h1 : Nat.card R ∣ Nat.card (Equiv.Perm (Wt ρ V)) :=
    Subgroup.card_dvd_of_injective _ hRinj
  have h2 : Nat.card (Equiv.Perm (Wt ρ V)) = (Nat.card (Wt ρ V)).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.card_eq_fintype_card]
  rw [h2] at h1
  exact h1.trans (Nat.factorial_dvd_factorial hcard)

theorem card_le_pow_finrank (ρ : X →* End F W) (hρ : Function.Injective ρ)
    (V : Subgroup X) [Finite V] (hV : IsMulCommutative V) (hinv : (Nat.card V : F) ≠ 0)
    {s : ℕ} (hs : 0 < s) (hexp : ∀ v ∈ V, v ^ s = 1) :
    Nat.card V ≤ s ^ finrank F W := by
  obtain ⟨hfin, hcard⟩ := finite_card_weights ρ V hV
  have := Fintype.ofFinite (Wt ρ V)
  have hroot : ∀ (χ : Wt ρ V) (v : V), χ.1 v ^ s = 1 := by
    intro χ v
    rw [← χ.2.pow v s]
    have : (v ^ s : V) = 1 := Subtype.ext (hexp v v.2)
    rw [this, χ.2.one]
  let Θ : V → (Wt ρ V → {u : F // u ^ s = 1}) := fun v χ => ⟨χ.1 v, hroot χ v⟩
  have hΘ : Function.Injective Θ := by
    intro v v' h
    have hc : ρ ((v * v'⁻¹ : V) : X) = (1 : F) • (1 : End F W) := by
      refine eq_smul_one_of_weights ρ V hV hinv _ 1 (fun χ hχ w hw => ?_)
      have h1 : χ v = χ v' := congrArg Subtype.val (congrFun h ⟨χ, hχ⟩)
      calc ρ ((v * v'⁻¹ : V) : X) w = ρ (v : X) (ρ ((v'⁻¹ : V) : X) w) := by
            rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
        _ = ρ (v : X) (χ v'⁻¹ • w) := by rw [hw v'⁻¹]
        _ = (χ v' * χ v'⁻¹) • w := by rw [map_smul, hw v, smul_smul, h1, mul_comm]
        _ = (1 : F) • w := by rw [hχ.inv, mul_inv_cancel₀ (hχ.ne_zero v')]
    rw [one_smul] at hc
    have h2 : ((v * v'⁻¹ : V) : X) = 1 := hρ (by rw [hc, map_one])
    have h3 : v * v'⁻¹ = 1 := Subtype.ext h2
    exact mul_inv_eq_one.mp h3
  have hfinroot : Finite {u : F // u ^ s = 1} := finite_nthRoots F s hs
  have h1 : Nat.card V ≤ Nat.card (Wt ρ V → {u : F // u ^ s = 1}) :=
    Nat.card_le_card_of_injective Θ hΘ
  have h2 : Nat.card (Wt ρ V → {u : F // u ^ s = 1}) ≤ s ^ Nat.card (Wt ρ V) := by
    rw [Nat.card_fun]
    exact Nat.pow_le_pow_left (card_nthRoots_le F s hs) _
  exact h1.trans (h2.trans (Nat.pow_le_pow_right hs hcard))

end CFSG.SignalizerFunctorTheorem.NonLocalExc
