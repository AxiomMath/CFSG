module

public import CFSG.Quasithin.Background.G12Stmts

public section

namespace CFSG.Quasithin.G11.P4InspEnd

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

private theorem two_self (x : U) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

private theorem omega_indep (ω : GLV U) (hω : ∀ x, ω (ω x) + ω x + x = 0) {v : U} (hv : v ≠ 0) :
    ω v ≠ 0 ∧ ω v ≠ v := by
  refine ⟨fun h => hv (by rw [← ω.symm_apply_apply v, h, map_zero]), fun h => hv ?_⟩
  have := hω v
  simp only [h, two_self v, zero_add] at this
  exact this

theorem p4inspend_f4_core (f : LinearMap.BilinForm (ZMod 2) U) (hf : IsSymplectic f) (v : U)
    (hv : v ≠ 0) (ω : GLV U) (hω : ∀ x, ω (ω x) + ω x + x = 0) (t : GLV U) (htsp : t ∈ spSub f)
    (htω : t * ω = ω * t) (ht1 : t ≠ 1) (htfix : ∀ u, f v u = 0 → t u = u) : False := by
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have haa : ∀ a : ZMod 2, a + a = 0 := by decide
  have hab : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  obtain ⟨hωv0, hωvv⟩ := omega_indep ω hω hv
  have hfl : ∀ a b y : U, f (a + b) y = f a y + f b y := fun a b y => by
    rw [map_add, LinearMap.add_apply]
  obtain ⟨x, hx⟩ : ∃ x : U, t x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact ht1 (LinearEquiv.ext hcon)
  have hfx : f v x = 1 := (hz _).resolve_left (fun h => hx (htfix x h))
  have hA : ∀ y, f v y = 0 → f (t x + x) y = 0 := by
    intro y hy
    have h1 := htsp x y
    rw [htfix y hy] at h1
    rw [hfl, h1]
    exact haa _
  have hB : ∀ y, f v y = 1 → f (t x + x) y = f (t x + x) x := by
    intro y hy
    have hyx : f v (y + x) = 0 := by
      rw [map_add, hy, hfx]
      exact haa _
    have h1 := hA (y + x) hyx
    rw [map_add] at h1
    exact hab _ _ h1
  obtain ⟨c, hc⟩ : ∃ c : ZMod 2, c = f (t x + x) x := ⟨_, rfl⟩
  have hwv : t x + x + c • v = 0 := by
    apply hf.2
    intro y
    rw [hfl (t x + x) (c • v) y, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rcases hz (f v y) with h | h
    · rw [h, hA y h, mul_zero, add_zero]
    · rw [h, hB y h, mul_one, hc]
      exact haa _
  have htx : t x = x + c • v := by
    have h1 : t x + (x + c • v) = 0 := by
      rw [← add_assoc]
      exact hwv
    calc t x = t x + (x + c • v + (x + c • v)) := by rw [two_self, add_zero]
      _ = (t x + (x + c • v)) + (x + c • v) := (add_assoc _ _ _).symm
      _ = x + c • v := by rw [h1, zero_add]
  have hc1 : c = 1 := by
    refine (hz c).resolve_left fun h => hx ?_
    rw [htx, h, zero_smul, add_zero]
  have hC : ∀ y, t y = y + f v y • v := by
    intro y
    rcases hz (f v y) with h | h
    · rw [h, zero_smul, add_zero]
      exact htfix y h
    · have hyx : f v (y + x) = 0 := by
        rw [map_add, h, hfx]
        exact haa _
      have h1 := htfix (y + x) hyx
      rw [map_add, htx, hc1, one_smul] at h1
      rw [h, one_smul]
      calc t y = t y + (x + v + (x + v)) := by rw [two_self, add_zero]
        _ = (t y + (x + v)) + (x + v) := (add_assoc _ _ _).symm
        _ = y + x + (x + v) := by rw [h1]
        _ = y + v := by rw [add_assoc y x (x + v), ← add_assoc x x v, two_self x, zero_add]
  have hC' := hC (ω x)
  have hcomm' : t (ω x) = ω (t x) := congrArg (fun F : GLV U => F x) htω
  rw [hcomm', htx, hc1, one_smul, map_add] at hC'
  have h3 : ω v = f v (ω x) • v := add_left_cancel hC'
  rcases hz (f v (ω x)) with h | h
  · rw [h, zero_smul] at h3
    exact hωv0 h3
  · rw [h, one_smul] at h3
    exact hωvv h3

theorem p4inspend_f4_false (f : LinearMap.BilinForm (ZMod 2) U) (hf : IsSymplectic f) (v : U)
    (hv : v ≠ 0) (hvp : v ∈ perp f v) (Q P : Subgroup (GLV U)) (hPQ : P ≤ Q) (hPsp : P ≤ spSub f)
    (hQ : ∀ y ∈ Q, ∃ g : ↥(perp f v) →ₗ[ZMod 2] ZMod 2, g ⟨v, hvp⟩ = 0 ∧
      ∀ u : ↥(perp f v), y (u : U) = (u : U) + g u • v)
    (ω : GLV U) (hω : ∀ x, ω (ω x) + ω x + x = 0) (hPω : ∀ p ∈ P, p * ω = ω * p)
    (hP : 2 < Nat.card ↥P) : False := by
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hmem : ∀ u : U, u ∈ perp f v ↔ f v u = 0 := fun u => LinearMap.mem_ker
  obtain ⟨hωv0, hωvv⟩ := omega_indep ω hω hv
  have hind : ∀ c d : ZMod 2, c • v = d • ω v → d = 0 := by
    intro c d h
    rcases hz c with rfl | rfl <;> rcases hz d with rfl | rfl
    · rfl
    · simp only [zero_smul, one_smul] at h
      exact absurd h.symm hωv0
    · simp only [zero_smul, one_smul] at h
      exact absurd h hv
    · simp only [one_smul] at h
      exact absurd h.symm hωvv
  have hex : ∀ p : ↥P, ∃ g : ↥(perp f v) →ₗ[ZMod 2] ZMod 2, g ⟨v, hvp⟩ = 0 ∧
      ∀ u : ↥(perp f v), ((p : ↥P) : GLV U) (u : U) = (u : U) + g u • v :=
    fun p => hQ p (hPQ p.2)
  choose g hg0 hg using hex
  have hvan : ∀ (p : ↥P) (u : U) (hu : u ∈ perp f v) (hωu : ω u ∈ perp f v),
      g p ⟨u, hu⟩ = 0 := by
    intro p u hu hωu
    have hc : ((p : ↥P) : GLV U) * ω = ω * ((p : ↥P) : GLV U) := hPω p p.2
    have h1 : ((p : ↥P) : GLV U) (ω u) = ω (((p : ↥P) : GLV U) u) :=
      congrArg (fun F : GLV U => F u) hc
    rw [hg p ⟨ω u, hωu⟩, hg p ⟨u, hu⟩, map_add, map_smul] at h1
    have h2 : g p ⟨ω u, hωu⟩ • v = g p ⟨u, hu⟩ • ω v := add_left_cancel h1
    exact hind _ _ h2
  obtain ⟨u₁, hu₁p, hu₁⟩ : ∃ u₁ : U, f v u₁ = 0 ∧
      ∀ u : U, f v u = 0 → f v (ω u) = 0 ∨ f v (ω (u + u₁)) = 0 := by
    by_cases h : ∃ w : U, f v w = 0 ∧ f v (ω w) ≠ 0
    · obtain ⟨w, hw0, hw1⟩ := h
      refine ⟨w, hw0, fun u hu => ?_⟩
      rcases hz (f v (ω u)) with h0 | h1
      · exact Or.inl h0
      · right
        have hw1' : f v (ω w) = 1 := (hz _).resolve_left hw1
        rw [map_add, map_add, h1, hw1']
        decide
    · push Not at h
      exact ⟨0, by simp, fun u hu => Or.inl (h u hu)⟩
  have hu₁mem : u₁ ∈ perp f v := (hmem u₁).2 hu₁p
  have hPfin : Finite ↥P := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype ↥P := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod 2) < Fintype.card ↥P := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card]
    exact hP
  obtain ⟨p, p', hpp', hF⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun q : ↥P => g q ⟨u₁, hu₁mem⟩) hcard
  have hp0 : ((p'⁻¹ * p : ↥P) : GLV U) ≠ 1 := by
    intro h
    apply hpp'
    have h' : p'⁻¹ * p = 1 := Subtype.ext h
    exact (inv_mul_eq_one.1 h').symm
  have hp0u : ((p'⁻¹ * p : ↥P) : GLV U) u₁ = u₁ := by
    have e1 : ((p : ↥P) : GLV U) u₁ = u₁ + g p ⟨u₁, hu₁mem⟩ • v := hg p ⟨u₁, hu₁mem⟩
    have e2 : ((p' : ↥P) : GLV U) u₁ = u₁ + g p' ⟨u₁, hu₁mem⟩ • v := hg p' ⟨u₁, hu₁mem⟩
    have e3 : ((p : ↥P) : GLV U) u₁ = ((p' : ↥P) : GLV U) u₁ := by
      rw [e1, e2]
      have hF' : g p ⟨u₁, hu₁mem⟩ = g p' ⟨u₁, hu₁mem⟩ := hF
      rw [hF']
    show (((p' : ↥P) : GLV U)⁻¹ : GLV U) (((p : ↥P) : GLV U) u₁) = u₁
    rw [e3]
    exact ((p' : ↥P) : GLV U).symm_apply_apply u₁
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ↥P, p₀ = p'⁻¹ * p := ⟨_, rfl⟩
  rw [← hp₀] at hp0 hp0u
  have hg0u₁ : g p₀ ⟨u₁, hu₁mem⟩ = 0 := by
    have h1 := hg p₀ ⟨u₁, hu₁mem⟩
    rw [hp0u] at h1
    have h2 : g p₀ ⟨u₁, hu₁mem⟩ • v = 0 := by
      have : u₁ + 0 = u₁ + g p₀ ⟨u₁, hu₁mem⟩ • v := by rw [add_zero]; exact h1
      exact (add_left_cancel this).symm
    exact (smul_eq_zero.1 h2).resolve_right hv
  have hfix : ∀ u : U, f v u = 0 → ((p₀ : ↥P) : GLV U) u = u := by
    intro u hu
    have humem : u ∈ perp f v := (hmem u).2 hu
    have hg0 : g p₀ ⟨u, humem⟩ = 0 := by
      rcases hu₁ u hu with h | h
      · exact hvan p₀ u humem ((hmem _).2 h)
      · have hsum : u + u₁ ∈ perp f v := (perp f v).add_mem humem hu₁mem
        have h1 := hvan p₀ (u + u₁) hsum ((hmem _).2 h)
        have h2 : g p₀ ⟨u + u₁, hsum⟩ = g p₀ ⟨u, humem⟩ + g p₀ ⟨u₁, hu₁mem⟩ :=
          map_add (g p₀) (⟨u, humem⟩ : ↥(perp f v)) ⟨u₁, hu₁mem⟩
        rw [h2, hg0u₁, add_zero] at h1
        exact h1
    have := hg p₀ ⟨u, humem⟩
    rw [hg0, zero_smul, add_zero] at this
    exact this
  exact p4inspend_f4_core f hf v hv ω hω ((p₀ : ↥P) : GLV U) (hPsp p₀.2) (hPω p₀ p₀.2) hp0 hfix

end CFSG.Quasithin.G11.P4InspEnd
