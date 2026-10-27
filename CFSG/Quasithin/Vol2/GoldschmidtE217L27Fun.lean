module

public import CFSG.Quasithin.Vol2.GoldschmidtE217L27Grp

public section

namespace CFSG.Quasithin

namespace E217L27

section Word

variable {Γ : Type*} [Group Γ]

theorem inv_eq_of_sq {y : Γ} (h : y * y = 1) : y⁻¹ = y := inv_eq_of_mul_eq_one_right h

theorem word_lemma {av aa ac as as' avsv avs'v : Γ} (T1 : av * aa * ac = 1)
    (T3 : ac * as * as' = 1) (T2 : aa * avsv * avs'v = 1) (c2 : avsv * avs'v = avs'v * avsv)
    (D1 : avs'v * as' = as * avsv) (D2 : as' * avs'v * (as' * avs'v) = 1) (ha : aa * aa = 1)
    (hc : ac * ac = 1) (hs : as * as = 1) (hs' : as' * as' = 1) (h1 : avsv * avsv = 1)
    (h2 : avs'v * avs'v = 1) : av = 1 := by
  have e1 : av = ac * aa := by
    have : av = (aa * ac)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact T1)
    rw [this, mul_inv_rev, inv_eq_of_sq ha, inv_eq_of_sq hc]
  have e2 : ac = as' * as := by
    have : ac = (as * as')⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact T3)
    rw [this, mul_inv_rev, inv_eq_of_sq hs, inv_eq_of_sq hs']
  have e3 : aa = avsv * avs'v := by
    have : aa = (avsv * avs'v)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact T2)
    rw [this, mul_inv_rev, inv_eq_of_sq h1, inv_eq_of_sq h2, c2]
  calc av = ac * aa := e1
    _ = (as' * as) * (avsv * avs'v) := by rw [← e2, ← e3]
    _ = as' * (as * avsv) * avs'v := by group
    _ = as' * (avs'v * as') * avs'v := by rw [D1]
    _ = (as' * avs'v) * (as' * avs'v) := by group
    _ = 1 := D2

end Word

section Phi

variable {Y X Γ : Type*} [Group Y] [Group X] [Group Γ]

structure Triple3 (a b c : Γ) : Prop where
  prod : a * b * c = 1
  comm₁₂ : a * b = b * a
  comm₁₃ : a * c = c * a
  comm₂₃ : b * c = c * b

theorem Triple3.swap {a b c : Γ} (h : Triple3 a b c) : Triple3 a c b :=
  ⟨by rw [mul_assoc, ← h.comm₂₃, ← mul_assoc]; exact h.prod, h.comm₁₃, h.comm₁₂, h.comm₂₃.symm⟩

theorem Triple3.conj {a b c : Γ} (h : Triple3 a b c) (g : Γ) :
    Triple3 (g * a * g⁻¹) (g * b * g⁻¹) (g * c * g⁻¹) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc g * a * g⁻¹ * (g * b * g⁻¹) * (g * c * g⁻¹) = g * (a * b * c) * g⁻¹ := by group
      _ = 1 := by rw [h.prod]; group
  · calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h.comm₁₂]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  · calc g * a * g⁻¹ * (g * c * g⁻¹) = g * (a * c) * g⁻¹ := by group
      _ = g * (c * a) * g⁻¹ := by rw [h.comm₁₃]
      _ = g * c * g⁻¹ * (g * a * g⁻¹) := by group
  · calc g * b * g⁻¹ * (g * c * g⁻¹) = g * (b * c) * g⁻¹ := by group
      _ = g * (c * b) * g⁻¹ := by rw [h.comm₂₃]
      _ = g * c * g⁻¹ * (g * b * g⁻¹) := by group

structure BFun (ρ : Y →* Γ) (f : Y → Γ) (T' : Subgroup Y) (x' zh : Y) : Prop where
  sq : ∀ g, f g * f g = 1
  inv_T : ∀ g, ∀ t ∈ T', f (g * t) = f g
  conj : ∀ g₁ g₂, f (g₁ * g₂) = ρ g₁ * f g₂ * (ρ g₁)⁻¹
  triple : Triple3 (f 1) (f zh) (f zh⁻¹)
  fix : ∀ g, ∀ t ∈ T', f (t * g) * f (t * x' * g) = f g * f (x' * g)
  beta_sq : ∀ g, f g * f (x' * g) * (f g * f (x' * g)) = 1

theorem BFun.one_eq_one {ρ : Y →* Γ} {f : Y → Γ} {T' : Subgroup Y} {x' zh : Y}
    (hf : BFun ρ f T' x' zh) {K : Subgroup X} (hS : Setting X K) (hOdd : OddOracle K)
    (p : Y →* X) (hp : Function.Surjective p) {v z : X} (hv : v ∈ K) (hv2 : v * v = 1)
    (hv1 : v ≠ 1) (hz : z ∈ K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hvz : v * z * v⁻¹ = z⁻¹)
    (hpx : p x' = v) (hpz : p zh = z) (hT' : ∀ g : Y, p g * v = v * p g → g ∈ T') :
    f 1 = 1 := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  obtain ⟨φ, hφ⟩ : ∃ φ : X → Γ, ∀ g : Y, φ (p g * v * (p g)⁻¹) = f g := by
    classical
    refine ⟨fun u => if h : ∃ g : Y, p g * v * (p g)⁻¹ = u then f h.choose else 1, fun g => ?_⟩
    have h : ∃ g' : Y, p g' * v * (p g')⁻¹ = p g * v * (p g)⁻¹ := ⟨g, rfl⟩
    show (if h' : ∃ g' : Y, p g' * v * (p g')⁻¹ = p g * v * (p g)⁻¹ then f h'.choose else 1) =
      f g
    rw [dite_eq_left_of_eq_true (eq_true h)]
    have hc : p h.choose * v * (p h.choose)⁻¹ = p g * v * (p g)⁻¹ := h.choose_spec
    set c := h.choose with hcdef
    have hcom : p (g⁻¹ * c) * v = v * p (g⁻¹ * c) := by
      have e : p c * v = p g * v * (p g)⁻¹ * p c := by
        calc p c * v = (p c * v * (p c)⁻¹) * p c := by group
          _ = (p g * v * (p g)⁻¹) * p c := by rw [hc]
      calc p (g⁻¹ * c) * v = (p g)⁻¹ * (p c * v) := by simp [map_mul, mul_assoc]
        _ = (p g)⁻¹ * (p g * v * (p g)⁻¹ * p c) := by rw [e]
        _ = v * p (g⁻¹ * c) := by simp [map_mul, mul_assoc]
    have := hf.inv_T g (g⁻¹ * c) (hT' _ hcom)
    rw [mul_inv_cancel_left] at this
    exact this
  have orb_v : ∃ g : Y, p g * v * (p g)⁻¹ = v := ⟨1, by simp⟩
  have orb_conj : ∀ u : X, (∃ g : Y, p g * v * (p g)⁻¹ = u) → ∀ w : X,
      ∃ g : Y, p g * v * (p g)⁻¹ = w * u * w⁻¹ := by
    rintro u ⟨g, rfl⟩ w
    obtain ⟨h, rfl⟩ := hp w
    exact ⟨h * g, by simp [map_mul, mul_assoc]⟩
  have phi_conj : ∀ u : X, (∃ g : Y, p g * v * (p g)⁻¹ = u) → ∀ h : Y,
      φ (p h * u * (p h)⁻¹) = ρ h * φ u * (ρ h)⁻¹ := by
    rintro u ⟨g, rfl⟩ h
    have e : p h * (p g * v * (p g)⁻¹) * (p h)⁻¹ = p (h * g) * v * (p (h * g))⁻¹ := by
      simp [map_mul, mul_assoc]
    rw [e, hφ, hφ, hf.conj]
  have phi_sq : ∀ u : X, (∃ g : Y, p g * v * (p g)⁻¹ = u) → φ u * φ u = 1 := by
    rintro u ⟨g, rfl⟩
    rw [hφ]
    exact hf.sq g
  have phi_conj' : ∀ u : X, (∃ g : Y, p g * v * (p g)⁻¹ = u) → ∀ w : X, ∃ h : Y,
      p h = w ∧ φ (w * u * w⁻¹) = ρ h * φ u * (ρ h)⁻¹ := by
    intro u hu w
    obtain ⟨h, rfl⟩ := hp w
    exact ⟨h, rfl, phi_conj u hu h⟩
  have hφ1 : φ v = f 1 := by simpa using hφ 1
  have hφa : φ (z * v * z⁻¹) = f zh := by simpa [hpz] using hφ zh
  have hφc : φ (z⁻¹ * v * z) = f zh⁻¹ := by simpa [hpz] using hφ zh⁻¹
  have T1 : Triple3 (φ v) (φ (z * v * z⁻¹)) (φ (z⁻¹ * v * z)) := by
    rw [hφ1, hφa, hφc]
    exact hf.triple
  have hT : ∀ u ζ : X, u ∈ K → ζ ∈ K → ζ ^ 3 = 1 → ζ ≠ 1 → u * ζ * u⁻¹ = ζ⁻¹ →
      (∃ g : Y, p g * v * (p g)⁻¹ = u) →
      Triple3 (φ u) (φ (ζ * u * ζ⁻¹)) (φ (ζ⁻¹ * u * ζ)) := by
    intro u ζ hu hζ hζ3 hζ1 huζ huo
    obtain ⟨κ, hκ, hκu, hκζ⟩ :=
      hS.exists_conj_of_inv' hv hv2 hz hz3 hz1 hvz hu hζ hζ3 hζ1 huζ
    have eu : u = κ⁻¹ * v * κ := by rw [← hκu]; group
    have e1 : ζ * u * ζ⁻¹ = κ⁻¹ * ((κ * ζ * κ⁻¹) * v * (κ * ζ * κ⁻¹)⁻¹) * κ := by
      rw [← hκu]; group
    have e2 : ζ⁻¹ * u * ζ = κ⁻¹ * ((κ * ζ * κ⁻¹)⁻¹ * v * (κ * ζ * κ⁻¹)) * κ := by
      rw [← hκu]; group
    obtain ⟨h, hh, -⟩ := phi_conj' v orb_v κ⁻¹
    have key : ∀ w : X, (∃ g : Y, p g * v * (p g)⁻¹ = w) →
        φ (κ⁻¹ * w * κ) = ρ h * φ w * (ρ h)⁻¹ := by
      intro w hw
      have := phi_conj w hw h
      rwa [hh, inv_inv] at this
    have hζ₀ : Triple3 (φ v) (φ ((κ * ζ * κ⁻¹) * v * (κ * ζ * κ⁻¹)⁻¹))
        (φ ((κ * ζ * κ⁻¹)⁻¹ * v * (κ * ζ * κ⁻¹))) := by
      rcases hκζ with h' | h'
      · rw [h']; exact T1
      · rw [h', inv_inv]; exact T1.swap
    have o1 := orb_conj v orb_v (κ * ζ * κ⁻¹)
    have o2 : ∃ g : Y, p g * v * (p g)⁻¹ = (κ * ζ * κ⁻¹)⁻¹ * v * (κ * ζ * κ⁻¹) := by
      have := orb_conj v orb_v (κ * ζ * κ⁻¹)⁻¹
      rwa [inv_inv] at this
    have g1 : φ u = ρ h * φ v * (ρ h)⁻¹ := by rw [eu]; exact key v orb_v
    have g2 : φ (ζ * u * ζ⁻¹) =
        ρ h * φ ((κ * ζ * κ⁻¹) * v * (κ * ζ * κ⁻¹)⁻¹) * (ρ h)⁻¹ := by
      rw [e1]; exact key _ o1
    have g3 : φ (ζ⁻¹ * u * ζ) =
        ρ h * φ ((κ * ζ * κ⁻¹)⁻¹ * v * (κ * ζ * κ⁻¹)) * (ρ h)⁻¹ := by
      rw [e2]; exact key _ o2
    rw [g1, g2, g3]
    exact hζ₀.conj (ρ h)
  obtain ⟨c₀, z', -, hc₀2, hc₀z, hc₀v, hz'K, hz'3, hz'1, hcz', hwz'⟩ :=
    hS.exists_config hOdd hv hv2 hv1 hz hz3 hz1 hvz
  set c := z⁻¹ * v * z with hcdef
  have hcK : c ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hz) hv) hz
  have hc2 : c * c = 1 := by
    calc c * c = z⁻¹ * (v * v) * z := by rw [hcdef]; group
      _ = 1 := by rw [hv2]; group
  have oc : ∃ g : Y, p g * v * (p g)⁻¹ = c := by
    have := orb_conj v orb_v z⁻¹
    rwa [inv_inv] at this
  have T3 := hT c z' hcK hz'K hz'3 hz'1 hcz' oc
  set s := z' * c * z'⁻¹ with hsdef
  set s' := z'⁻¹ * c * z' with hs'def
  have os : ∃ g : Y, p g * v * (p g)⁻¹ = s := orb_conj c oc z'
  have os' : ∃ g : Y, p g * v * (p g)⁻¹ = s' := by
    have := orb_conj c oc z'⁻¹
    rwa [inv_inv] at this
  have hvca : v * c * v⁻¹ = z * v * z⁻¹ := by
    have e1 : v * z⁻¹ * v⁻¹ = z := by
      have := congrArg (fun t => t⁻¹) hvz
      simpa [mul_assoc] using this
    calc v * c * v⁻¹ = (v * z⁻¹ * v⁻¹) * v * (v * z * v⁻¹) := by rw [hcdef]; group
      _ = z * v * z⁻¹ := by rw [e1, hvz]
  have q : ∀ w : X, (∃ g : Y, p g * v * (p g)⁻¹ = w) →
      φ (v * w * v⁻¹) = ρ x' * φ w * (ρ x')⁻¹ := by
    intro w hw
    have := phi_conj w hw x'
    rwa [hpx] at this
  have T2 : Triple3 (φ (v * c * v⁻¹)) (φ (v * s * v⁻¹)) (φ (v * s' * v⁻¹)) := by
    rw [q c oc, q s os, q s' os']
    exact T3.conj (ρ x')
  rw [hvca] at T2
  have hc₀zi : c₀ * z⁻¹ = z⁻¹ * c₀ := by
    calc c₀ * z⁻¹ = z⁻¹ * (z * c₀) * z⁻¹ := by group
      _ = z⁻¹ * (c₀ * z) * z⁻¹ := by rw [hc₀z]
      _ = z⁻¹ * c₀ := by group
  have hc₀c : c₀ * c = c * c₀ := by
    calc c₀ * c = (c₀ * z⁻¹) * v * z := by rw [hcdef]; group
      _ = z⁻¹ * (c₀ * v) * z := by rw [hc₀zi]; group
      _ = z⁻¹ * (v * c₀) * z := by rw [hc₀v]
      _ = z⁻¹ * v * (c₀ * z) := by group
      _ = z⁻¹ * v * (z * c₀) := by rw [hc₀z]
      _ = c * c₀ := by rw [hcdef]; group
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hc₀z' : c₀ * z' * c₀⁻¹ = z'⁻¹ := by
    have h1 : c₀ * z' = c⁻¹ * z' * c * c₀ := by
      calc c₀ * z' = c⁻¹ * (c * c₀ * z') := by group
        _ = c⁻¹ * (z' * (c * c₀)) := by rw [hwz']
        _ = c⁻¹ * z' * c * c₀ := by group
    calc c₀ * z' * c₀⁻¹ = c⁻¹ * z' * c := by rw [h1]; group
      _ = c * z' * c⁻¹ := by rw [hci]
      _ = z'⁻¹ := hcz'
  have hc₀cc : c₀ * c * c₀⁻¹ = c := by rw [hc₀c]; group
  have hc₀s : c₀ * s * c₀⁻¹ = s' := by
    calc c₀ * s * c₀⁻¹ = (c₀ * z' * c₀⁻¹) * (c₀ * c * c₀⁻¹) * (c₀ * z' * c₀⁻¹)⁻¹ := by
          rw [hsdef]; group
      _ = z'⁻¹ * c * z' := by rw [hc₀z', hc₀cc]; group
      _ = s' := rfl
  obtain ⟨gs, hgs⟩ := os
  obtain ⟨gs', hgs'⟩ := os'
  obtain ⟨th, hth⟩ := hp (c₀ * v)
  have hthT : th ∈ T' := by
    refine hT' th ?_
    rw [hth]
    calc c₀ * v * v = c₀ := by rw [mul_assoc, hv2, mul_one]
      _ = v * (c₀ * v) := by
        calc c₀ = c₀ * (v * v) := by rw [hv2, mul_one]
          _ = (c₀ * v) * v := (mul_assoc _ _ _).symm
          _ = (v * c₀) * v := by rw [hc₀v]
          _ = v * (c₀ * v) := mul_assoc _ _ _
  have hfφ : ∀ (h g : Y) (u : X), p g * v * (p g)⁻¹ = u →
      f (h * g) = φ (p h * u * (p h)⁻¹) := by
    intro h g u hu
    rw [← hφ (h * g), ← hu]
    congr 1
    simp [map_mul, mul_assoc]
  have hvv : v⁻¹ * v⁻¹ = 1 := by rw [hvi, hv2]
  have e_a : c₀ * v * s * (c₀ * v)⁻¹ = v * s' * v⁻¹ := by
    calc c₀ * v * s * (c₀ * v)⁻¹ = v * c₀ * s * (v * c₀)⁻¹ := by rw [hc₀v]
      _ = v * (c₀ * s * c₀⁻¹) * v⁻¹ := by group
      _ = v * s' * v⁻¹ := by rw [hc₀s]
  have e_b : c₀ * v * (v * s * v⁻¹) * (c₀ * v)⁻¹ = s' := by
    calc c₀ * v * (v * s * v⁻¹) * (c₀ * v)⁻¹
        = c₀ * ((v * v) * s * (v⁻¹ * v⁻¹)) * c₀⁻¹ := by group
      _ = c₀ * s * c₀⁻¹ := by rw [hv2, hvv]; group
      _ = s' := hc₀s
  have hgs2 : p (x' * gs) * v * (p (x' * gs))⁻¹ = v * s * v⁻¹ := by
    rw [map_mul, hpx, ← hgs]
    group
  have D1 : φ (v * s' * v⁻¹) * φ s' = φ s * φ (v * s * v⁻¹) := by
    have h0 := hf.fix gs th hthT
    have h1 : f (th * gs) = φ (v * s' * v⁻¹) := by rw [hfφ th gs s hgs, hth, e_a]
    have h2 : f (th * x' * gs) = φ s' := by
      rw [mul_assoc, hfφ th (x' * gs) _ hgs2, hth, e_b]
    have h3 : f gs = φ s := by
      have := hφ gs
      rw [hgs] at this
      exact this.symm
    have h4 : f (x' * gs) = φ (v * s * v⁻¹) := by rw [hfφ x' gs s hgs, hpx]
    rw [h1, h2, h3, h4] at h0
    exact h0
  have D2 : φ s' * φ (v * s' * v⁻¹) * (φ s' * φ (v * s' * v⁻¹)) = 1 := by
    have h0 := hf.beta_sq gs'
    have h3 : f gs' = φ s' := by
      have := hφ gs'
      rw [hgs'] at this
      exact this.symm
    have h4 : f (x' * gs') = φ (v * s' * v⁻¹) := by rw [hfφ x' gs' s' hgs', hpx]
    rw [h3, h4] at h0
    exact h0
  have hoa : ∃ g : Y, p g * v * (p g)⁻¹ = z * v * z⁻¹ := orb_conj v orb_v z
  have os2 : ∃ g : Y, p g * v * (p g)⁻¹ = v * s * v⁻¹ := orb_conj s ⟨gs, hgs⟩ v
  have os2' : ∃ g : Y, p g * v * (p g)⁻¹ = v * s' * v⁻¹ := orb_conj s' ⟨gs', hgs'⟩ v
  have key := word_lemma T1.prod T3.prod T2.prod T2.comm₂₃ D1 D2 (phi_sq _ hoa) (phi_sq _ oc)
    (phi_sq _ ⟨gs, hgs⟩) (phi_sq _ ⟨gs', hgs'⟩) (phi_sq _ os2) (phi_sq _ os2')
  rw [← hφ1]
  exact key

end Phi

end E217L27

end CFSG.Quasithin
