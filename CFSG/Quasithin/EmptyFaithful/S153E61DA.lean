module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

namespace S153E61D

variable {Γ : Type*} [Group Γ]

open Classical in
noncomputable def parityBit (U : Subgroup Γ) (x : Γ) : ZMod 2 := if x ∈ U then 0 else 1

theorem parityBit_eq_zero_iff {U : Subgroup Γ} {x : Γ} : parityBit U x = 0 ↔ x ∈ U := by
  unfold parityBit
  split_ifs with h <;> simp [h]

theorem parityBit_one {U : Subgroup Γ} : parityBit U 1 = 0 :=
  parityBit_eq_zero_iff.2 U.one_mem

theorem parityBit_mul {U : Subgroup Γ} {a b : Γ} (h : a ∉ U → b ∉ U → a * b ∈ U) :
    parityBit U (a * b) = parityBit U a + parityBit U b := by
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
  · simp [parityBit, ha, hb, U.mul_mem ha hb]
  · have hab : a * b ∉ U := fun hab => hb (by simpa using U.mul_mem (U.inv_mem ha) hab)
    simp [parityBit, ha, hb, hab]
  · have hab : a * b ∉ U := fun hab => ha (by simpa using U.mul_mem hab (U.inv_mem hb))
    simp [parityBit, ha, hb, hab]
  · have hab := h ha hb
    simp only [parityBit, ha, hb, hab, ite_true, ite_false]
    decide

theorem eq_zero_or_of_add_eq_zero {a b c : ZMod 2} (h : a + b + c = 0) : a = 0 ∨ b = 0 ∨ c = 0 := by
  revert a b c
  decide

theorem not_all_one_of_add_eq {x y z u w : ZMod 2} (h₁ : x + y + z = 0) (h₂ : u = w) (hx : x = 1)
    (hu : u + y = 1) (hw : w + z = 1) : False := by
  revert x y z u w
  decide

section Pigeon

variable {V : Subgroup Γ} {d : Γ}

theorem pow_three_aux (hd3 : d ^ 3 = 1) : d * d = d⁻¹ ∧ d⁻¹ * d⁻¹ = d := by
  have h1 : d * d * d = 1 := by simpa [pow_succ, mul_assoc] using hd3
  have h2 : d * d = d⁻¹ := eq_inv_of_mul_eq_one_left h1
  refine ⟨h2, ?_⟩
  calc d⁻¹ * d⁻¹ = (d * d) * (d * d) := by rw [h2]
    _ = (d * d * d) * d := by group
    _ = d := by rw [h1, one_mul]

theorem comm3 {a b v : Γ} (hbv : b * v = v * b) (hav : a * v = v * a) :
    a * b * v = v * a * b := by
  calc a * b * v = a * (b * v) := mul_assoc _ _ _
    _ = a * (v * b) := by rw [hbv]
    _ = (a * v) * b := (mul_assoc _ _ _).symm
    _ = (v * a) * b := by rw [hav]

theorem pigeon_eq_one (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hd3 : d ^ 3 = 1)
    (hdV : ∀ v ∈ V, d * v * d⁻¹ ∈ V) (hdfix : ∀ v ∈ V, d * v * d⁻¹ = v → v = 1) {v : Γ}
    (hv : v ∈ V) : d⁻¹ * v * d ∈ V ∧ v * (d * v * d⁻¹) * (d⁻¹ * v * d) = 1 := by
  obtain ⟨h2, h2'⟩ := pow_three_aux hd3
  have hv1 : d * v * d⁻¹ ∈ V := hdV v hv
  have e2 : d * (d * v * d⁻¹) * d⁻¹ = d⁻¹ * v * d := by
    calc d * (d * v * d⁻¹) * d⁻¹ = (d * d) * v * (d⁻¹ * d⁻¹) := by group
      _ = d⁻¹ * v * d := by rw [h2, h2']
  have hv2 : d⁻¹ * v * d ∈ V := by
    rw [← e2]
    exact hdV _ hv1
  refine ⟨hv2, ?_⟩
  have hwV : v * (d * v * d⁻¹) * (d⁻¹ * v * d) ∈ V := V.mul_mem (V.mul_mem hv hv1) hv2
  apply hdfix _ hwV
  have e1 : d * (v * (d * v * d⁻¹) * (d⁻¹ * v * d)) * d⁻¹ =
      (d * v * d⁻¹) * (d * (d * v * d⁻¹) * d⁻¹) * (d * (d⁻¹ * v * d) * d⁻¹) := by group
  have e3 : d * (d⁻¹ * v * d) * d⁻¹ = v := by group
  rw [e1, e2, e3]
  exact comm3 (hVab _ hv2 _ hv) (hVab _ hv1 _ hv)

end Pigeon

theorem parityBit_eq_one_of_not_mem {U : Subgroup Γ} {x : Γ} (hx : x ∉ U) : parityBit U x = 1 := by
  simp [parityBit, hx]

theorem parityBit_congr {U : Subgroup Γ} {x y : Γ} (h : x ∈ U ↔ y ∈ U) :
    parityBit U x = parityBit U y := by
  by_cases hx : x ∈ U
  · simp [parityBit, hx, h.1 hx]
  · simp [parityBit, hx, mt h.2 hx]

section Main

variable {I B P V U Z : Subgroup Γ} {d τ : Γ}

theorem exists_fixed_point (hVB : V ≤ B) (hτU : τ ∈ U) (hℓ : ∃ ℓ ∈ V, ℓ ∈ U ∧ τ * ℓ * τ⁻¹ ≠ ℓ)
    (hZ : ∀ u ∈ U, ∀ w ∈ U, u * w * u⁻¹ * w⁻¹ ∈ Z) (hZc : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z)
    (hZsq : ∀ z ∈ Z, z * z = 1) (hZ2 : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ 1 → z' ≠ 1 → z = z')
    (hE : ∃ e ∈ B, e ∈ U ∧ e ∉ V) : ∃ e ∈ B, e ∈ U ∧ e ∉ V ∧ τ * e * τ⁻¹ = e := by
  obtain ⟨e₀, he₀B, he₀U, he₀V⟩ := hE
  by_cases h : τ * e₀ * τ⁻¹ = e₀
  · exact ⟨e₀, he₀B, he₀U, he₀V, h⟩
  obtain ⟨ℓ, hℓV, hℓU, hℓτ⟩ := hℓ
  have hz₀ : τ * e₀ * τ⁻¹ * e₀⁻¹ ∈ Z := hZ τ hτU e₀ he₀U
  have hz₁ : τ * ℓ * τ⁻¹ * ℓ⁻¹ ∈ Z := hZ τ hτU ℓ hℓU
  have hz₀ne : τ * e₀ * τ⁻¹ * e₀⁻¹ ≠ 1 := fun h' => h (mul_inv_eq_one.1 h')
  have hz₁ne : τ * ℓ * τ⁻¹ * ℓ⁻¹ ≠ 1 := fun h' => hℓτ (mul_inv_eq_one.1 h')
  have hz01 := hZ2 _ hz₀ _ hz₁ hz₀ne hz₁ne
  refine ⟨e₀ * ℓ, B.mul_mem he₀B (hVB hℓV), U.mul_mem he₀U hℓU, ?_, ?_⟩
  · intro hV
    exact he₀V (by simpa using V.mul_mem hV (V.inv_mem hℓV))
  · calc τ * (e₀ * ℓ) * τ⁻¹
        = ((τ * e₀ * τ⁻¹ * e₀⁻¹) * e₀) * ((τ * ℓ * τ⁻¹ * ℓ⁻¹) * ℓ) := by group
      _ = (τ * e₀ * τ⁻¹ * e₀⁻¹) * (e₀ * (τ * ℓ * τ⁻¹ * ℓ⁻¹)) * ℓ := by group
      _ = (τ * e₀ * τ⁻¹ * e₀⁻¹) * ((τ * ℓ * τ⁻¹ * ℓ⁻¹) * e₀) * ℓ := by
          rw [← hZc _ hz₁ e₀ he₀U]
      _ = ((τ * e₀ * τ⁻¹ * e₀⁻¹) * (τ * e₀ * τ⁻¹ * e₀⁻¹)) * e₀ * ℓ := by
          rw [← hz01]; group
      _ = e₀ * ℓ := by rw [hZsq _ hz₀, one_mul]

theorem star_abstract (hVB : V ≤ B) (hVc : ∀ v ∈ V, ∀ x ∈ B, v * x = x * v)
    (hdI : d ∈ I) (hd3 : d ^ 3 = 1) (hdV : ∀ v ∈ V, d * v * d⁻¹ ∈ V)
    (hdfix : ∀ v ∈ V, d * v * d⁻¹ = v → v = 1) (hdB : ∀ x ∈ B, d * x * d⁻¹ * x⁻¹ ∈ V)
    (hτU : τ ∈ U) (hτd : τ * d * τ⁻¹ * d ∈ P) (hPU : ∀ p ∈ P, ∀ u ∈ U, p * u * p⁻¹ ∈ U)
    (hVU : ∀ v ∈ V, ∀ w ∈ V, v ∉ U → w ∉ U → v * w ∈ U)
    (hℓ : ∃ ℓ ∈ V, ℓ ∈ U ∧ τ * ℓ * τ⁻¹ ≠ ℓ)
    (hZ : ∀ u ∈ U, ∀ w ∈ U, u * w * u⁻¹ * w⁻¹ ∈ Z) (hZc : ∀ z ∈ Z, ∀ u ∈ U, z * u = u * z)
    (hZsq : ∀ z ∈ Z, z * z = 1) (hZ2 : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ 1 → z' ≠ 1 → z = z')
    (hE : ∃ e ∈ B, e ∈ U ∧ e ∉ V)
    (htrans : ∀ a ∈ B, a ∉ V → ∀ b ∈ B, b ∉ V → ∃ γ ∈ I, γ * a * γ⁻¹ * b⁻¹ ∈ V) :
    ∀ x ∈ B, ∃ γ ∈ I, γ * x * γ⁻¹ ∈ U := by
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => hVc a ha b (hVB hb)
  have hdI' : d⁻¹ ∈ I := I.inv_mem hdI
  obtain ⟨h2, h2'⟩ := pow_three_aux hd3
  have hbit : ∀ v ∈ V, parityBit U v + parityBit U (d * v * d⁻¹) +
      parityBit U (d⁻¹ * v * d) = 0 := by
    intro v hv
    obtain ⟨hv2, hprod⟩ := pigeon_eq_one hVab hd3 hdV hdfix hv
    have hv1 := hdV v hv
    have h1 := parityBit_mul (U := U) (a := v * (d * v * d⁻¹)) (b := d⁻¹ * v * d)
      (hVU _ (V.mul_mem hv hv1) _ hv2)
    have h3 := parityBit_mul (U := U) (a := v) (b := d * v * d⁻¹) (hVU _ hv _ hv1)
    rw [hprod, parityBit_one, h3] at h1
    exact h1.symm
  have hVcase : ∀ v ∈ V, ∃ γ ∈ I, γ * v * γ⁻¹ ∈ U := by
    intro v hv
    rcases eq_zero_or_of_add_eq_zero (hbit v hv) with h | h | h
    · exact ⟨1, I.one_mem, by simpa using parityBit_eq_zero_iff.1 h⟩
    · exact ⟨d, hdI, parityBit_eq_zero_iff.1 h⟩
    · exact ⟨d⁻¹, hdI', by rw [inv_inv]; exact parityBit_eq_zero_iff.1 h⟩
  obtain ⟨e, heB, heU, heV, hτe⟩ := exists_fixed_point hVB hτU hℓ hZ hZc hZsq hZ2 hE
  have hc₁ : d * e * d⁻¹ * e⁻¹ ∈ V := hdB e heB
  have hdeB : d * e * d⁻¹ ∈ B := by
    have := B.mul_mem (hVB hc₁) heB
    simpa [mul_assoc] using this
  have hc₂ : d⁻¹ * e * d * e⁻¹ ∈ V := by
    have h3 := V.mul_mem (hdB _ hdeB) hc₁
    have e1 : d * (d * e * d⁻¹) * d⁻¹ * (d * e * d⁻¹)⁻¹ * (d * e * d⁻¹ * e⁻¹) =
        (d * d) * e * (d⁻¹ * d⁻¹) * e⁻¹ := by group
    rw [e1, h2, h2'] at h3
    exact h3
  have hsym : parityBit U (d * e * d⁻¹ * e⁻¹) = parityBit U (d⁻¹ * e * d * e⁻¹) := by
    have hf : ∀ c, c * e ∈ U ↔ c ∈ U := fun c =>
      ⟨fun h => by simpa using U.mul_mem h (U.inv_mem heU), fun h => U.mul_mem h heU⟩
    have hpP : τ * d * τ⁻¹ * d ∈ P := hτd
    have hτd' : τ * d * τ⁻¹ = (τ * d * τ⁻¹ * d) * d⁻¹ := by group
    have key : τ * (d * e * d⁻¹) * τ⁻¹ =
        (τ * d * τ⁻¹ * d) * (d⁻¹ * e * d) * (τ * d * τ⁻¹ * d)⁻¹ := by
      calc τ * (d * e * d⁻¹) * τ⁻¹ = (τ * d * τ⁻¹) * (τ * e * τ⁻¹) * (τ * d * τ⁻¹)⁻¹ := by group
        _ = ((τ * d * τ⁻¹ * d) * d⁻¹) * e * ((τ * d * τ⁻¹ * d) * d⁻¹)⁻¹ := by rw [← hτd', hτe]
        _ = (τ * d * τ⁻¹ * d) * (d⁻¹ * e * d) * (τ * d * τ⁻¹ * d)⁻¹ := by group
    have hτU' : ∀ x, τ * x * τ⁻¹ ∈ U ↔ x ∈ U := fun x =>
      ⟨fun h => by
        have := U.mul_mem (U.mul_mem (U.inv_mem hτU) h) hτU
        simpa [mul_assoc] using this,
       fun h => U.mul_mem (U.mul_mem hτU h) (U.inv_mem hτU)⟩
    have hpU' : ∀ x, (τ * d * τ⁻¹ * d) * x * (τ * d * τ⁻¹ * d)⁻¹ ∈ U ↔ x ∈ U := fun x =>
      ⟨fun h => by
        have := hPU _ (P.inv_mem hpP) _ h
        simpa [mul_assoc] using this,
       fun h => hPU _ hpP x h⟩
    have hiff : d * e * d⁻¹ ∈ U ↔ d⁻¹ * e * d ∈ U := by
      rw [← hτU', key, hpU']
    apply parityBit_congr
    rw [← hf (d * e * d⁻¹ * e⁻¹), ← hf (d⁻¹ * e * d * e⁻¹)]
    simpa using hiff
  have hF : ∀ v ∈ V, ∃ γ ∈ I, γ * (e * v) * γ⁻¹ ∈ U := by
    intro v hv
    obtain ⟨hv2, -⟩ := pigeon_eq_one hVab hd3 hdV hdfix hv
    have hv1 := hdV v hv
    have hbv := hbit v hv
    have hg₁ : d * (e * v) * d⁻¹ = e * ((d * e * d⁻¹ * e⁻¹) * (d * v * d⁻¹)) := by
      have hc : (d * e * d⁻¹ * e⁻¹) * e = e * (d * e * d⁻¹ * e⁻¹) := hVc _ hc₁ e heB
      calc d * (e * v) * d⁻¹ = ((d * e * d⁻¹ * e⁻¹) * e) * (d * v * d⁻¹) := by group
        _ = e * (d * e * d⁻¹ * e⁻¹) * (d * v * d⁻¹) := by rw [hc]
        _ = e * ((d * e * d⁻¹ * e⁻¹) * (d * v * d⁻¹)) := by group
    have hg₂ : d⁻¹ * (e * v) * d⁻¹⁻¹ = e * ((d⁻¹ * e * d * e⁻¹) * (d⁻¹ * v * d)) := by
      have hc : (d⁻¹ * e * d * e⁻¹) * e = e * (d⁻¹ * e * d * e⁻¹) := hVc _ hc₂ e heB
      calc d⁻¹ * (e * v) * d⁻¹⁻¹ = ((d⁻¹ * e * d * e⁻¹) * e) * (d⁻¹ * v * d) := by group
        _ = e * (d⁻¹ * e * d * e⁻¹) * (d⁻¹ * v * d) := by rw [hc]
        _ = e * ((d⁻¹ * e * d * e⁻¹) * (d⁻¹ * v * d)) := by group
    have hmem : ∀ a, e * a ∈ U ↔ a ∈ U := fun a =>
      ⟨fun h => by simpa using U.mul_mem (U.inv_mem heU) h, fun h => U.mul_mem heU h⟩
    by_contra hcon
    push Not at hcon
    have n0 : v ∉ U := fun h => hcon 1 I.one_mem (by simpa using (hmem v).2 h)
    have n1 : (d * e * d⁻¹ * e⁻¹) * (d * v * d⁻¹) ∉ U := fun h =>
      hcon d hdI (by rw [hg₁]; exact (hmem _).2 h)
    have n2 : (d⁻¹ * e * d * e⁻¹) * (d⁻¹ * v * d) ∉ U := fun h =>
      hcon d⁻¹ hdI' (by rw [hg₂]; exact (hmem _).2 h)
    have b1 := parityBit_mul (U := U) (a := d * e * d⁻¹ * e⁻¹) (b := d * v * d⁻¹)
      (hVU _ hc₁ _ hv1)
    have b2 := parityBit_mul (U := U) (a := d⁻¹ * e * d * e⁻¹) (b := d⁻¹ * v * d)
      (hVU _ hc₂ _ hv2)
    exact not_all_one_of_add_eq hbv hsym (parityBit_eq_one_of_not_mem n0)
      (by rw [← b1]; exact parityBit_eq_one_of_not_mem n1)
      (by rw [← b2]; exact parityBit_eq_one_of_not_mem n2)
  intro x hx
  by_cases hxV : x ∈ V
  · exact hVcase x hxV
  · obtain ⟨γ, hγI, hγ⟩ := htrans x hx hxV e heB heV
    have hxe : γ * x * γ⁻¹ = e * (γ * x * γ⁻¹ * e⁻¹) := by
      calc γ * x * γ⁻¹ = (γ * x * γ⁻¹ * e⁻¹) * e := by group
        _ = e * (γ * x * γ⁻¹ * e⁻¹) := hVc _ hγ e heB
    obtain ⟨γ', hγ'I, hγ'⟩ := hF _ hγ
    refine ⟨γ' * γ, I.mul_mem hγ'I hγI, ?_⟩
    have e1 : γ' * γ * x * (γ' * γ)⁻¹ = γ' * (γ * x * γ⁻¹) * γ'⁻¹ := by group
    rw [e1, hxe]
    exact hγ'

end Main


end S153E61D

end CFSG.Quasithin
