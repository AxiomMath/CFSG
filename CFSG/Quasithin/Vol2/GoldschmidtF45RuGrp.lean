module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.H13.F45Ru

section Fix

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem normal_pgroup_fixes [Finite Ω] [MulAction.IsPretransitive G Ω] {p : ℕ} [Fact p.Prime]
    (Q : Subgroup G) [hQn : Q.Normal] (hQ : IsPGroup p Q) (hd : ¬ p ∣ Nat.card Ω) (q : G)
    (hq : q ∈ Q) (w : Ω) : q • w = w := by
  have hmod := hQ.card_modEq_card_fixedPoints Ω
  have hinv : ∀ (g : G) (u : Ω), u ∈ MulAction.fixedPoints Q Ω →
      g • u ∈ MulAction.fixedPoints Q Ω := by
    intro g u hu
    rw [MulAction.mem_fixedPoints] at hu ⊢
    intro q'
    have h1 : g⁻¹ * (q' : G) * g ∈ Q := by
      have := hQn.conj_mem (q' : G) q'.2 g⁻¹
      simpa [mul_assoc] using this
    have h2 := hu ⟨g⁻¹ * (q' : G) * g, h1⟩
    rw [Subgroup.smul_def] at h2 ⊢
    have h3 : (g⁻¹ * (q' : G) * g) • u = u := h2
    calc (q' : G) • g • u = g • ((g⁻¹ * (q' : G) * g) • u) := by
          rw [← mul_smul, ← mul_smul]
          congr 1
          group
      _ = g • u := by rw [h3]
  have hall : ∀ u : Ω, u ∈ MulAction.fixedPoints Q Ω := by
    by_cases hne : (MulAction.fixedPoints Q Ω).Nonempty
    · obtain ⟨u₀, hu₀⟩ := hne
      intro u
      obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G u₀ u
      exact hinv g u₀ hu₀
    · exfalso
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have h0 : Nat.card (MulAction.fixedPoints Q Ω) = 0 := by
        rw [hne]; simp
      rw [h0] at hmod
      exact hd ((Nat.modEq_zero_iff_dvd).1 hmod)
  have := MulAction.mem_fixedPoints.mp (hall w) ⟨q, hq⟩
  rwa [Subgroup.smul_def] at this

end Fix

section Orbit

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem card_stabilizer_mul_ncard_orbit [Finite G] (x : Ω) :
    Nat.card (MulAction.stabilizer G x) * (MulAction.orbit G x).ncard = Nat.card G := by
  rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]

end Orbit

end CFSG.Quasithin.H13.F45Ru
