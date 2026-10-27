module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubConn
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubPartner

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {T : Track Γ G}
  {a b : ℤ} {H : Subgroup G}

theorem partner_step (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m₀ : ℤ} (hm : b - a = 2 * m₀)
    {M : Subgroup G} (hMH : M ≤ H) {γ w γ' : V}
    (hγ : γ ∈ MulAction.orbit ↥H (T.line.vert a)) (hγw : Γ.Adj γ w) (hp : IsPartner Γ H γ w γ')
    (hM : ∀ x y, Γ.Adj γ x → Γ.Adj γ y → ∃ k ∈ M, k • γ = γ ∧ k • x = y) {m : G} (hmM : m ∈ M)
    {u' : V} (hu' : u' ∈ MulAction.orbit ↥H (T.line.vert a)) (hc : CommonNbr Γ u' (m • γ)) :
    ∃ n ∈ M, n • γ' = u' := by
  obtain ⟨hne, w', hw'u, hw'm⟩ := hc
  have hw'γ : Γ.Adj γ (m⁻¹ • w') := by
    have := (F.adj_smul m⁻¹ _ _).2 hw'm
    rwa [inv_smul_smul] at this
  obtain ⟨k, hkM, hkγ, hkw⟩ := hM _ _ hw'γ hγw
  have hkγ' : k⁻¹ • γ = γ := by
    rw [inv_smul_eq_iff]
    exact hkγ.symm
  have hkw' : k⁻¹ • w = m⁻¹ • w' := by
    rw [inv_smul_eq_iff]
    exact hkw.symm
  have hnM : m * k⁻¹ ∈ M := M.mul_mem hmM (M.inv_mem hkM)
  have hnγ : (m * k⁻¹) • γ = m • γ := by rw [mul_smul, hkγ']
  have hnw : (m * k⁻¹) • w = w' := by rw [mul_smul, hkw', smul_inv_smul]
  have hp' := hp.smul F (hMH hnM)
  rw [hnγ, hnw] at hp'
  have hmγA : m • γ ∈ MulAction.orbit ↥H (T.line.vert a) := by
    obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup.1 hγ
    exact mem_orbit_subgroup.2 ⟨m * h, H.mul_mem (hMH hmM) hh, by rw [mul_smul]⟩
  have horb : u' ∈ MulAction.orbit ↥H (m • γ) := by
    rw [MulAction.orbit_eq_iff.2 hmγA]
    exact hu'
  obtain ⟨u₀, -, huniq⟩ := fan46_partner hS F hm hmγA hw'm
  refine ⟨m * k⁻¹, hnM, ?_⟩
  have e1 := huniq _ hp'
  have e2 := huniq u' ⟨horb, hne, hw'u⟩
  rw [e1, e2]

theorem fan46_orbit_closure (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m₀ : ℤ}
    (hm : b - a = 2 * m₀) {M : Subgroup G} (hMH : M ≤ H) {γ₁ w₁ γ₂ : V}
    (hγ₁ : γ₁ ∈ MulAction.orbit ↥H (T.line.vert a)) (hγw : Γ.Adj γ₁ w₁)
    (hp : IsPartner Γ H γ₁ w₁ γ₂)
    (hM₁ : ∀ x y, Γ.Adj γ₁ x → Γ.Adj γ₁ y → ∃ k ∈ M, k • γ₁ = γ₁ ∧ k • x = y)
    (hM₂ : ∀ x y, Γ.Adj γ₂ x → Γ.Adj γ₂ y → ∃ k ∈ M, k • γ₂ = γ₂ ∧ k • x = y) :
    ∀ u ∈ MulAction.orbit ↥H (T.line.vert a),
      (∃ n ∈ M, n • γ₁ = u) ∨ (∃ n ∈ M, n • γ₂ = u) := by
  have hγ₂ : γ₂ ∈ MulAction.orbit ↥H (T.line.vert a) := by
    have := hp.1
    rwa [MulAction.orbit_eq_iff.2 hγ₁] at this
  have hp' : IsPartner Γ H γ₂ w₁ γ₁ := by
    refine ⟨?_, fun h => hp.2.1 h.symm, hγw⟩
    rw [MulAction.orbit_eq_iff.2 hγ₂]
    exact hγ₁
  have hmem : ∀ {γ : V}, γ ∈ MulAction.orbit ↥H (T.line.vert a) → ∀ {n : G}, n ∈ M →
      n • γ ∈ MulAction.orbit ↥H (T.line.vert a) := by
    intro γ hγ n hn
    obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup.1 hγ
    exact mem_orbit_subgroup.2 ⟨n * h, H.mul_mem (hMH hn) hh, by rw [mul_smul]⟩
  have hS' := fan46_conn hS F (S := {u | (∃ n ∈ M, n • γ₁ = u) ∨ (∃ n ∈ M, n • γ₂ = u)})
    (by
      rintro u (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
      · exact hmem hγ₁ hn
      · exact hmem hγ₂ hn)
    ⟨γ₁, Or.inl ⟨1, M.one_mem, one_smul _ _⟩⟩
    (by
      rintro u (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩) u' hu' hc
      · exact Or.inr (partner_step hS F hm hMH hγ₁ hγw hp hM₁ hn hu' hc)
      · exact Or.inl (partner_step hS F hm hMH hγ₂ hp.2.2 hp' hM₂ hn hu' hc))
  intro u hu
  have : u ∈ {u | (∃ n ∈ M, n • γ₁ = u) ∨ (∃ n ∈ M, n • γ₂ = u)} := by
    rw [hS']
    exact hu
  exact this

theorem fan46_fix (hS : SubgraphProp T a b H) (F : FanTree Γ G) {m₀ : ℤ} (hm : b - a = 2 * m₀)
    {M : Subgroup G} (hMH : M ≤ H) {γ₁ w₁ γ₂ : V}
    (hγ₁ : γ₁ ∈ MulAction.orbit ↥H (T.line.vert a)) (hγw : Γ.Adj γ₁ w₁)
    (hp : IsPartner Γ H γ₁ w₁ γ₂)
    (hM₁ : ∀ x y, Γ.Adj γ₁ x → Γ.Adj γ₁ y → ∃ k ∈ M, k • γ₁ = γ₁ ∧ k • x = y)
    (hM₂ : ∀ x y, Γ.Adj γ₂ x → Γ.Adj γ₂ y → ∃ k ∈ M, k • γ₂ = γ₂ ∧ k • x = y)
    {U : Subgroup G} (hU₁ : ∀ g ∈ U, g • γ₁ = γ₁) (hU₂ : ∀ g ∈ U, g • γ₂ = γ₂)
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ fixSet G (MulAction.orbit ↥H (T.line.vert a)) := by
  intro g hg u hu
  have key : ∀ (γ : V), (∀ g ∈ U, g • γ = γ) → ∀ n ∈ M, g • n • γ = n • γ := by
    intro γ hγ n hn
    have h1 : n⁻¹ * g * n ∈ U := by
      have := (Subgroup.mem_normalizer_iff.1 (hMU (M.inv_mem hn)) g).1 hg
      simpa using this
    have := hγ _ h1
    rw [mul_smul, mul_smul, inv_smul_eq_iff] at this
    exact this
  rcases fan46_orbit_closure hS F hm hMH hγ₁ hγw hp hM₁ hM₂ u hu with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · exact key γ₁ hU₁ n hn
  · exact key γ₂ hU₂ n hn

end CFSG.Quasithin.Fan86
