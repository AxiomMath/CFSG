module

public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.EmptyFaithful.S153E58C

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

theorem lkf_out_three {X : Type} [Group X] (hΛ : IsPSL 3 2 1 X) :
    Subgroup.center X = ⊥ ∧ Nat.card (MulAut X) ≤ 2 * Nat.card X := by
  refine ⟨SBc11.center_eq_bot_of_list (Or.inl hΛ), ?_⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_slThree_of_isPSL hΛ
  have e' : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    e.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2))
  rw [Nat.card_congr (MulAut.congr e').toEquiv, SBc11.card_of_isPSL_three_two hΛ,
    S153E58.card_mulAut_statedSL_three_two]

theorem lkf_cent_normalizes {G : Type*} [Group G] {Γ Λ : Subgroup G}
    (hgn : ∀ a ∈ Γ, ∀ y ∈ Λ, a * y * a⁻¹ ∈ Λ) :
    Γ ≤ Subgroup.normalizer ((Γ ⊓ Subgroup.centralizer (Λ : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Γ, ∀ c ∈ Γ ⊓ Subgroup.centralizer (Λ : Set G),
      g * c * g⁻¹ ∈ Γ ⊓ Subgroup.centralizer (Λ : Set G) := by
    rintro g hg c ⟨hcΓ, hcC⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem hg hcΓ) (Γ.inv_mem hg), Subgroup.mem_centralizer_iff.2 ?_⟩
    intro l hl
    have hl' : g⁻¹ * l * g ∈ Λ := by
      simpa using hgn g⁻¹ (Γ.inv_mem hg) l hl
    have h1 := Subgroup.mem_centralizer_iff.1 hcC _ hl'
    calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * l := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  have := key g⁻¹ (Γ.inv_mem hg) _ hc
  simpa [mul_assoc] using this

theorem lkf_eq_bot_of_primes {G : Type*} [Group G] [Finite G] {Γ C : Subgroup G} (hCΓ : C ≤ Γ)
    (hn : Γ ≤ Subgroup.normalizer (C : Set G)) (hO : CFSG.Open.pCoreOf 2 Γ = ⊥)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥C → p = 2) : C = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
  have hC2 : IsPGroup 2 ↥C :=
    IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun hd hdvd => hp _ hd hdvd))
  have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCΓ hn hC2
  rw [hO] at this
  exact le_bot_iff.1 this

end CFSG.Quasithin
