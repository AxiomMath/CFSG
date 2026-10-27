module

public import CFSG.RankThree.PartOne.K159.AutSzAbs

public section

namespace CFSG.RankThree.PartOne.K159.SzAbs

open scoped Pointwise

variable {S X : Type*} [Group S] [MulAction S X]

theorem mem_smul_sylow_iff {p : ℕ} (g : S) (V : Sylow p S) (x : S) :
    x ∈ (g • V : Sylow p S) ↔ g⁻¹ * x * g ∈ (V : Subgroup S) := by
  have h1 : ((g • V : Sylow p S) : Subgroup S) = MulAut.conj g • (V : Subgroup S) := rfl
  show x ∈ ((g • V : Sylow p S) : Subgroup S) ↔ _
  rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem sylow_data_of_ovoid [Finite S] (hS : Nat.card S = 32537600)
    (Ω : Set X) (hΩ : ∀ g : S, ∀ x ∈ Ω, g • x ∈ Ω) (ω₀ : X) (hω₀ : ω₀ ∈ Ω)
    (htrans : ∀ x ∈ Ω, ∃ g : S, g • x = ω₀) (hΩcard : Ω.ncard = 1025)
    (U : Subgroup S) (hUcard : Nat.card U = 1024) (hUfix : ∀ u ∈ U, u • ω₀ = ω₀)
    (hUfree : ∀ u ∈ U, ∀ x ∈ Ω, x ≠ ω₀ → u • x = x → u = 1)
    (hstab : ∀ g : S, g • ω₀ = ω₀ → g ∈ Subgroup.normalizer (U : Set S)) :
    Nat.card (Sylow 2 S) = 1025 ∧
      ∀ V W : Sylow 2 S, V ≠ W → (V : Subgroup S) ⊓ (W : Subgroup S) = ⊥ := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hUsyl : Nat.card U = 2 ^ (Nat.card S).factorization 2 := by
    rw [hUcard, hS, factorization_two]
    norm_num
  let U₀ : Sylow 2 S := Sylow.ofCard U hUsyl
  have hU₀ : (U₀ : Subgroup S) = U := Sylow.coe_ofCard U hUsyl
  have hNstab : ∀ n : S, n ∈ Subgroup.normalizer (U : Set S) → n • ω₀ = ω₀ := by
    intro n hn
    by_contra hne
    have hx : n • ω₀ ∈ Ω := hΩ n ω₀ hω₀
    have hall : ∀ u ∈ U, u = 1 := by
      intro u hu
      refine hUfree u hu (n • ω₀) hx hne ?_
      have h1 : n⁻¹ * u * n ∈ U := by
        have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (U : Set S)).inv_mem hn) u).1 hu
        simpa using this
      calc u • (n • ω₀) = n • ((n⁻¹ * u * n) • ω₀) := by
            rw [← mul_smul, ← mul_smul]
            congr 1
            group
        _ = n • ω₀ := by rw [hUfix _ h1]
    have hbot : U = ⊥ := (Subgroup.eq_bot_iff_forall U).2 hall
    rw [hbot, Subgroup.card_bot] at hUcard
    omega
  have hstabeq : MulAction.stabilizer S ω₀ = Subgroup.normalizer (U : Set S) := by
    ext g
    exact ⟨fun hg => hstab g hg, fun hg => hNstab g hg⟩
  have horbit : MulAction.orbit S ω₀ = Ω := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact hΩ g ω₀ hω₀
    · intro hx
      obtain ⟨g, hg⟩ := htrans x hx
      exact ⟨g⁻¹, by show g⁻¹ • ω₀ = x; rw [← hg, inv_smul_smul]⟩
  have hcard : Nat.card (Sylow 2 S) = 1025 := by
    rw [Sylow.card_eq_index_normalizer U₀]
    have h1 : Subgroup.normalizer (U₀ : Set S) = Subgroup.normalizer (U : Set S) := by
      rw [← hU₀]
      rfl
    rw [h1, ← hstabeq, MulAction.index_stabilizer, horbit, hΩcard]
  refine ⟨hcard, ?_⟩
  intro V W hVW
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq S U₀ V
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq S U₀ W
  have hne : g • ω₀ ≠ h • ω₀ := by
    intro heq
    apply hVW
    have h1 : (h⁻¹ * g) • ω₀ = ω₀ := by rw [mul_smul, heq, inv_smul_smul]
    have hn : h⁻¹ * g ∈ Subgroup.normalizer ((U₀ : Subgroup S) : Set S) := by
      rw [hU₀]
      exact hstab _ h1
    have h2' : (h⁻¹ * g) • U₀ = U₀ := Sylow.smul_eq_iff_mem_normalizer.2 hn
    calc g • U₀ = h • ((h⁻¹ * g) • U₀) := by rw [← mul_smul]; simp
      _ = h • U₀ := by rw [h2']
  rw [eq_bot_iff]
  intro x hx
  have hxg : g⁻¹ * x * g ∈ U := by
    have := (mem_smul_sylow_iff g U₀ x).1 hx.1
    rwa [hU₀] at this
  have hxh : h⁻¹ * x * h ∈ U := by
    have := (mem_smul_sylow_iff h U₀ x).1 hx.2
    rwa [hU₀] at this
  have hxg' : x • (g • ω₀) = g • ω₀ := by
    have h1 : x * g = g * (g⁻¹ * x * g) := by group
    rw [← mul_smul, h1, mul_smul, hUfix _ hxg]
  have hxh' : x • (h • ω₀) = h • ω₀ := by
    have h1 : x * h = h * (h⁻¹ * x * h) := by group
    rw [← mul_smul, h1, mul_smul, hUfix _ hxh]
  have hy : (g⁻¹ * h) • ω₀ ∈ Ω := hΩ _ ω₀ hω₀
  have hyne : (g⁻¹ * h) • ω₀ ≠ ω₀ := by
    intro hh
    apply hne
    have : h • ω₀ = g • ω₀ := by
      calc h • ω₀ = g • ((g⁻¹ * h) • ω₀) := by rw [← mul_smul]; simp
        _ = g • ω₀ := by rw [hh]
    exact this.symm
  have hfix : (g⁻¹ * x * g) • ((g⁻¹ * h) • ω₀) = (g⁻¹ * h) • ω₀ := by
    have h1 : (g⁻¹ * x * g) * (g⁻¹ * h) = g⁻¹ * (x * h) := by group
    rw [← mul_smul, h1, mul_smul, mul_smul, hxh']
    exact (mul_smul _ _ _).symm
  have hu1 : g⁻¹ * x * g = 1 := hUfree _ hxg _ hy hyne hfix
  have : x = 1 := by
    have h1 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [h1, hu1]
    group
  exact Subgroup.mem_bot.2 this

end CFSG.RankThree.PartOne.K159.SzAbs
