module

public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.ZPInv

variable {Γ : Type} [Group Γ]

@[expose] def ZPSylow (Γ : Type) [Group Γ] : Prop :=
  ∀ P : Subgroup Γ, IsPGroup 2 ↥P → ¬ 2 ∣ P.index →
    ∀ c d : Γ, c ∈ centerOf P → d ∈ centerOf P → c ^ 2 = 1 → d ^ 2 = 1 → c ≠ 1 → d ≠ 1 → c = d

@[expose] def ZPUniq (Γ : Type) [Group Γ] : Prop :=
  Subgroup.center Γ = ⊥ ∧ ZPSylow Γ

theorem mem_centerOf_iff {P : Subgroup Γ} {c : Γ} :
    c ∈ centerOf P ↔ c ∈ P ∧ ∀ x ∈ P, x * c = c * x := by
  unfold centerOf
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem mem_centerOf_map_conj (S : Subgroup Γ) (g c : Γ) :
    c ∈ centerOf (S.map (MulAut.conj g).toMonoidHom) ↔ g⁻¹ * c * g ∈ centerOf S := by
  have hmem : ∀ x : Γ, x ∈ S.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ S := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [mem_centerOf_iff, mem_centerOf_iff, hmem]
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h x hx => ?_⟩
  · have := h (g * y * g⁻¹) ((hmem _).2 (by simpa [mul_assoc] using hy))
    calc y * (g⁻¹ * c * g) = g⁻¹ * ((g * y * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * y * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * c * g) * y := by group
  · have := h (g⁻¹ * x * g) ((hmem x).1 hx)
    calc x * c = g * ((g⁻¹ * x * g) * (g⁻¹ * c * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * c * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = c * x := by group

theorem center_eq_bot_of_simple (hs : IsSimpleGroup Γ) {N : ℕ} (hN : Nat.card Γ = N)
    (h2 : 2 ∣ N) (h3 : 2 < N) : Subgroup.center Γ = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Γ) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Γ := Subgroup.center_eq_top_iff.mp h
    have hp : (Nat.card Γ).Prime := Group.is_simple_iff_prime_card.mp hs
    rw [hN] at hp
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
    omega

theorem center_eq_bot_of_mulEquiv {Γ' : Type} [Group Γ'] (e : Γ ≃* Γ')
    (hc : Subgroup.center Γ' = ⊥) : Subgroup.center Γ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center Γ' := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    have := congrArg e (hx (e.symm y))
    simpa using this
  rw [hc, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (e.injective (by simpa using hx'))

theorem ZPSylow.of_mulEquiv {Γ' : Type} [Group Γ'] (e : Γ ≃* Γ') (h : ZPSylow Γ') :
    ZPSylow Γ := by
  intro P hP2 hPi c d hc' hd' hc2 hd2 hc1 hd1
  have hmap : ∀ x ∈ centerOf P, e x ∈ centerOf (P.map e.toMonoidHom) := by
    intro x hx
    rw [mem_centerOf_iff] at hx ⊢
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hx.2 y hy]
  have hP' : IsPGroup 2 ↥(P.map e.toMonoidHom) := hP2.map e.toMonoidHom
  have hi : ¬ 2 ∣ (P.map e.toMonoidHom).index := by
    rwa [Subgroup.index_map_of_bijective e.bijective]
  have := h _ hP' hi (e c) (e d) (hmap c hc') (hmap d hd') (by rw [← map_pow, hc2, map_one])
    (by rw [← map_pow, hd2, map_one]) (by simpa using hc1) (by simpa using hd1)
  exact e.injective this

theorem ZPUniq.of_mulEquiv {Γ' : Type} [Group Γ'] (e : Γ ≃* Γ') (h : ZPUniq Γ') : ZPUniq Γ :=
  ⟨center_eq_bot_of_mulEquiv e h.1, ZPSylow.of_mulEquiv e h.2⟩

theorem zpSylow_of_sylow [Finite Γ] (S : Subgroup Γ)
    (hS : IsPGroup 2 ↥S) (hSi : ¬ 2 ∣ S.index)
    (h : ∀ c d : Γ, c ∈ centerOf S → d ∈ centerOf S → c ^ 2 = 1 → d ^ 2 = 1 → c ≠ 1 → d ≠ 1 →
      c = d) : ZPSylow Γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP hPi c d hcP hdP hc2 hd2 hc1 hd1
  let A : Sylow 2 Γ := hS.toSylow hSi
  let B : Sylow 2 Γ := hP.toSylow hPi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ A B
  have hPS : P = S.map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  rw [hPS] at hcP hdP
  rw [mem_centerOf_map_conj] at hcP hdP
  have hconj : ∀ x : Γ, g⁻¹ * x * g = 1 → x = 1 := fun x hx => by
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, hx]
    group
  have hsq : ∀ x : Γ, x ^ 2 = 1 → (g⁻¹ * x * g) ^ 2 = 1 := fun x hx => by
    have : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
      rw [pow_two, pow_two]
      group
    rw [this, hx]
    group
  have := h _ _ hcP hdP (hsq c hc2) (hsq d hd2) (fun h1 => hc1 (hconj c h1))
    (fun h1 => hd1 (hconj d h1))
  calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * d * g) * g⁻¹ := by rw [this]
    _ = d := by group

theorem zpUniq_of_sylow [Finite Γ] (hc : Subgroup.center Γ = ⊥) (S : Subgroup Γ)
    (hS : IsPGroup 2 ↥S) (hSi : ¬ 2 ∣ S.index)
    (h : ∀ c d : Γ, c ∈ centerOf S → d ∈ centerOf S → c ^ 2 = 1 → d ^ 2 = 1 → c ≠ 1 → d ≠ 1 →
      c = d) : ZPUniq Γ :=
  ⟨hc, zpSylow_of_sylow S hS hSi h⟩

theorem zpUniq_of_central_subset [Finite Γ] (hc : Subgroup.center Γ = ⊥) (S : Subgroup Γ)
    (hS : IsPGroup 2 ↥S) (hSi : ¬ 2 ∣ S.index) (z : Γ)
    (h : ∀ c ∈ S, (∀ q ∈ S, c * q = q * c) → c = 1 ∨ c = z) : ZPUniq Γ := by
  refine zpUniq_of_sylow hc S hS hSi fun c d hcS hdS _ _ hc1 hd1 => ?_
  rw [mem_centerOf_iff] at hcS hdS
  rcases h c hcS.1 fun q hq => (hcS.2 q hq).symm with h1 | h1
  · exact absurd h1 hc1
  rcases h d hdS.1 fun q hq => (hdS.2 q hq).symm with h2 | h2
  · exact absurd h2 hd1
  rw [h1, h2]

end CFSG.Quasithin.ZPInv
