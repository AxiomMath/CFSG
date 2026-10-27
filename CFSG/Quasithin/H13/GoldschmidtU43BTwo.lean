module

public import CFSG.Quasithin.H13.GoldschmidtU43BElem

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem exists_pair_V4 : ∀ τ : V4, q τ = 0 → τ ≠ 0 → ∃ α β : V4, q α = 0 ∧ q β = 0 ∧
    bq α τ = 0 ∧ bq β τ = 0 ∧ α ≠ 0 ∧ α ≠ τ ∧ β ≠ 0 ∧ β ≠ τ ∧ α + β ≠ 0 ∧ α + β ≠ τ := by
  decide +kernel

namespace Swap

variable {z t w : G}

theorem Vg_le_U (s : Swap z t w) {v : G} (hv : v ∈ Vg z t) : v ∈ Uz z := by
  rcases (s.cm.mem_Vg_iff₄ _).1 hv with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact s.hyp.z_mem
  · exact s.ht.1
  · exact mul_mem s.hyp.z_mem s.ht.1

theorem theta_V (s : Swap z t w) {v : G} (hv : v ∈ Vg z t) :
    Multiplicative.toAdd (s.hyp.θ ⟨v, s.Vg_le_U hv⟩) = 0 ∨
      Multiplicative.toAdd (s.hyp.θ ⟨v, s.Vg_le_U hv⟩) =
        Multiplicative.toAdd (s.hyp.θ ⟨t, s.ht.1⟩) := by
  have hz1 : s.hyp.θ ⟨z, s.hyp.z_mem⟩ = 1 := (s.hyp.θ_eq_one_iff _).2 (Or.inr rfl)
  rcases (s.cm.mem_Vg_iff₄ _).1 hv with h | h | h | h
  · left
    have : (⟨v, s.Vg_le_U hv⟩ : ↥(Uz z)) = 1 := Subtype.ext h
    rw [this, map_one]; rfl
  · left
    have : s.hyp.θ ⟨v, s.Vg_le_U hv⟩ = 1 := (s.hyp.θ_eq_one_iff _).2 (Or.inr h)
    rw [this]; rfl
  · right
    have : (⟨v, s.Vg_le_U hv⟩ : ↥(Uz z)) = ⟨t, s.ht.1⟩ := Subtype.ext h
    rw [this]
  · right
    have : (⟨v, s.Vg_le_U hv⟩ : ↥(Uz z)) = ⟨z, s.hyp.z_mem⟩ * ⟨t, s.ht.1⟩ := Subtype.ext h
    rw [this, map_mul, hz1, one_mul]

theorem exists_two_good (s : Swap z t w) :
    ∃ a₁ a₂ : G, Good z t a₁ ∧ Good z t a₂ ∧ a₁ * a₂ ∉ Vg z t := by
  have h := s.hyp
  set τ : V4 := Multiplicative.toAdd (h.θ ⟨t, s.ht.1⟩) with hτ
  have hqτ : q τ = 0 := h.q_θ_eq_zero s.ht.1 s.ht.2.1
  have hτ0 : τ ≠ 0 := fun h0 => h.θ_ne_one s.ht.1 s.ht.2.2.1 s.ht.2.2.2
    (Multiplicative.toAdd.injective (by simpa [hτ] using h0))
  obtain ⟨α, β, hqα, hqβ, hbα, hbβ, hα0, hατ, hβ0, hβτ, hαβ0, hαβτ⟩ := exists_pair_V4 τ hqτ hτ0
  obtain ⟨u₁, hu₁⟩ := h.θ_surj (Multiplicative.ofAdd α)
  obtain ⟨u₂, hu₂⟩ := h.θ_surj (Multiplicative.ofAdd β)
  have hgood : ∀ (u : ↥(Uz z)) (γ : V4), h.θ u = Multiplicative.ofAdd γ → q γ = 0 → bq γ τ = 0 →
      γ ≠ 0 → γ ≠ τ → Good z t (u : G) := by
    intro u γ hu hq hb h0 hτ'
    refine ⟨⟨u.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_, ?_⟩
    · have := h.comm_eq u ⟨t, s.ht.1⟩
      rw [hu, toAdd_ofAdd, ← hτ, hb, zp_zero] at this
      calc (u : G) * t = ((u : G) * t * (u : G)⁻¹ * t⁻¹) * t * (u : G) := by group
        _ = t * (u : G) := by rw [this]; group
    · have := h.sq_eq u
      rw [hu, toAdd_ofAdd, hq, zp_zero, pow_two] at this
      exact this
    · intro hV
      rcases s.theta_V hV with e | e
      · rw [show (⟨(u : G), s.Vg_le_U hV⟩ : ↥(Uz z)) = u from rfl, hu, toAdd_ofAdd] at e
        exact h0 e
      · rw [show (⟨(u : G), s.Vg_le_U hV⟩ : ↥(Uz z)) = u from rfl, hu, toAdd_ofAdd] at e
        exact hτ' e
  refine ⟨u₁, u₂, hgood u₁ α hu₁ hqα hbα hα0 hατ, hgood u₂ β hu₂ hqβ hbβ hβ0 hβτ, fun hV => ?_⟩
  rcases s.theta_V hV with e | e
  · rw [show (⟨(u₁ : G) * u₂, s.Vg_le_U hV⟩ : ↥(Uz z)) = u₁ * u₂ from rfl, map_mul, hu₁, hu₂,
      toAdd_mul, toAdd_ofAdd, toAdd_ofAdd] at e
    exact hαβ0 e
  · rw [show (⟨(u₁ : G) * u₂, s.Vg_le_U hV⟩ : ↥(Uz z)) = u₁ * u₂ from rfl, map_mul, hu₁, hu₂,
      toAdd_mul, toAdd_ofAdd, toAdd_ofAdd] at e
    exact hαβτ e

end Swap

end CFSG.Quasithin.H13.U43
