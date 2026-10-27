module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem quat_eq_of_sq_eq_one :
    ∀ q : QuaternionGroup 2, q ^ 2 = 1 → q = QuaternionGroup.a 0 ∨ q = QuaternionGroup.a 2 := by
  decide

private theorem quat_comm_of_sq_ne :
    ∀ q q' : QuaternionGroup 2, q ^ 2 ≠ QuaternionGroup.a 2 → q * q' = q' * q := by
  decide

private theorem quat_a_one_sq :
    (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by
  decide

private theorem quat_commutator :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 *
      (QuaternionGroup.a 1)⁻¹ * (QuaternionGroup.xa 0)⁻¹ = QuaternionGroup.a 2 := by
  decide

private theorem quat_noncomm :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  decide

private theorem quaternion_package {Γ B : Type} [Group Γ] [Group B] (ρ : Γ →* MulAut B)
    (hρ : Nat.card ρ.range = 8)
    (hq : ∃ f : QuaternionGroup 2 →* MulAut B, Function.Injective f ∧ ∀ q, f q ∈ ρ.range)
    {z : MulAut B} (hz : z ∈ ρ.range) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∃ f : QuaternionGroup 2 →* MulAut B, Function.Injective f ∧ f.range = ρ.range ∧
      z = f (QuaternionGroup.a 2) := by
  obtain ⟨f, hf, hfq⟩ := hq
  have hfin : Finite ρ.range := Nat.finite_of_card_ne_zero (by rw [hρ]; norm_num)
  have hfr : f.range = ρ.range := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨q, rfl⟩
      exact hfq q
    · rw [hρ, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
      simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  refine ⟨f, hf, hfr, ?_⟩
  obtain ⟨q, rfl⟩ : z ∈ f.range := hfr ▸ hz
  have hq2 : q ^ 2 = 1 := hf (by rw [map_pow, hz2, map_one])
  rcases quat_eq_of_sq_eq_one q hq2 with rfl | rfl
  · exact absurd (by rw [← QuaternionGroup.one_def, map_one]) hz1
  · rfl

private theorem exists_mem_sylow_map_eq {Γ B : Type} [Group Γ] [Finite Γ] [Group B]
    (ρ : Γ →* MulAut B) (hρ : Nat.card ρ.range = 8) (S : Sylow 2 Γ) :
    ∀ u ∈ ρ.range, ∃ s ∈ (S : Subgroup Γ), ρ s = u := by
  intro u hu
  have hfin : Finite ρ.range := Nat.finite_of_card_ne_zero (by rw [hρ]; norm_num)
  have h1 : ((S : Subgroup Γ).map ρ.rangeRestrict).index ∣ (S : Subgroup Γ).index :=
    Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective
  have h2 : ((S : Subgroup Γ).map ρ.rangeRestrict).index ∣ 8 :=
    hρ ▸ Subgroup.index_dvd_card _
  have hcop : Nat.Coprime 8 (S : Subgroup Γ).index := by
    have h3 : Nat.Coprime 2 (S : Subgroup Γ).index :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 S.not_dvd_index
    simpa using h3.pow_left 3
  have h4 : ((S : Subgroup Γ).map ρ.rangeRestrict).index = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h1
  have h5 : (S : Subgroup Γ).map ρ.rangeRestrict = ⊤ := Subgroup.index_eq_one.mp h4
  have h6 : (⟨u, hu⟩ : ρ.range) ∈ (S : Subgroup Γ).map ρ.rangeRestrict := by
    rw [h5]
    trivial
  obtain ⟨s, hs, hsu⟩ := h6
  exact ⟨s, hs, congrArg Subtype.val hsu⟩

theorem exists_mem_inverting_inner {Γ B X : Type} [Group Γ] [Finite Γ] [Group B] [Group X]
    (ρ : Γ →* MulAut B) (σ : Γ →* MulAut X) (hρ : Nat.card ρ.range = 8)
    (hq : ∃ f : QuaternionGroup 2 →* MulAut B, Function.Injective f ∧ ∀ q, f q ∈ ρ.range)
    (Γ₁ : Subgroup Γ) (hΓ₁ : Γ₁.index ≤ 2) (hab : OutTwoAbelian X)
    (hexp : Γ₁.index = 2 → OutTwoExpTwo X)
    {z : MulAut B} (hz : z ∈ ρ.range) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∃ γ ∈ Γ₁, ρ γ = z ∧ σ γ ∈ inner X := by
  obtain ⟨f, -, hfr, hzf⟩ := quaternion_package ρ hρ hq hz hz2 hz1
  obtain ⟨S⟩ : Nonempty (Sylow 2 Γ) := inferInstance
  have hS := exists_mem_sylow_map_eq ρ hρ S
  let π : Γ →* Outer X := (QuotientGroup.mk' (inner X)).comp σ
  have hπ : IsPGroup 2 ((S : Subgroup Γ).map π) := S.isPGroup'.map _
  have hπ1 : ∀ g, π g = 1 → σ g ∈ inner X := fun g hg => (QuotientGroup.eq_one_iff _).mp hg
  have hmem : ∀ q, f q ∈ ρ.range := fun q => hfr ▸ ⟨q, rfl⟩
  have h0 : Γ₁.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show Γ₁.index = 1 ∨ Γ₁.index = 2 by omega) with h1 | h2
  · have hΓ : Γ₁ = ⊤ := Subgroup.index_eq_one.mp h1
    obtain ⟨s₁, hs₁, h₁⟩ := hS (f (QuaternionGroup.a 1)) (hmem _)
    obtain ⟨s₂, hs₂, h₂⟩ := hS (f (QuaternionGroup.xa 0)) (hmem _)
    have hcomm : π s₁ * π s₂ = π s₂ * π s₁ :=
      hab _ hπ _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩
    refine ⟨s₁ * s₂ * s₁⁻¹ * s₂⁻¹, by rw [hΓ]; exact Subgroup.mem_top _, ?_, hπ1 _ ?_⟩
    · have : ρ (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) = f (QuaternionGroup.a 1 * QuaternionGroup.xa 0 *
          (QuaternionGroup.a 1)⁻¹ * (QuaternionGroup.xa 0)⁻¹) := by
        simp only [map_mul, map_inv, h₁, h₂]
      rw [this, quat_commutator, hzf]
    · simp only [map_mul, map_inv]
      rw [hcomm]
      group
  · obtain ⟨s, hs, hρs⟩ := hS (f (QuaternionGroup.a 1)) (hmem _)
    refine ⟨s ^ 2, Subgroup.sq_mem_of_index_two h2 s, ?_, hπ1 _ ?_⟩
    · rw [map_pow, hρs, ← map_pow, quat_a_one_sq, hzf]
    · have h3 := hexp h2 _ hπ (π s) ⟨s, hs, rfl⟩
      rwa [← map_pow] at h3

theorem exists_mem_square_inverting_inner {Γ B X : Type} [Group Γ] [Finite Γ] [Group B]
    [Group X] (ρ : Γ →* MulAut B) (σ : Γ →* MulAut X) (hρ : Nat.card ρ.range = 8)
    (hq : ∃ f : QuaternionGroup 2 →* MulAut B, Function.Injective f ∧ ∀ q, f q ∈ ρ.range)
    (hcyc : CFSG.ClassicalInvolution.Nobq.OutTwoCyclic X)
    {z : MulAut B} (hz : z ∈ ρ.range) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) :
    ∃ γ : Γ, σ γ ∈ inner X ∧ ρ γ ^ 2 = z := by
  obtain ⟨f, hfinj, hfr, hzf⟩ := quaternion_package ρ hρ hq hz hz2 hz1
  obtain ⟨S⟩ : Nonempty (Sylow 2 Γ) := inferInstance
  have hS := exists_mem_sylow_map_eq ρ hρ S
  let π : Γ →* Outer X := (QuotientGroup.mk' (inner X)).comp σ
  have hπ : IsPGroup 2 ((S : Subgroup Γ).map π) := S.isPGroup'.map _
  have hπ1 : ∀ g, π g = 1 → σ g ∈ inner X := fun g hg => (QuotientGroup.eq_one_iff _).mp hg
  have hmem : ∀ q, f q ∈ ρ.range := fun q => hfr ▸ ⟨q, rfl⟩
  have hcy := hcyc _ hπ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥((S : Subgroup Γ).map π))
  obtain ⟨s₀, hs₀, hgs₀⟩ := g.2
  have hdec : ∀ s ∈ (S : Subgroup Γ), ∃ k ∈ (S : Subgroup Γ), π k = 1 ∧
      ∃ n : ℤ, s = k * s₀ ^ n := by
    intro s hs
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨π s, ⟨s, hs, rfl⟩⟩)
    have hn' : π s = π s₀ ^ n := by
      have := congrArg Subtype.val hn
      rw [Subgroup.coe_zpow, ← hgs₀] at this
      exact this.symm
    refine ⟨s * (s₀ ^ n)⁻¹, (S : Subgroup Γ).mul_mem hs
      ((S : Subgroup Γ).inv_mem ((S : Subgroup Γ).zpow_mem hs₀ n)), ?_, n, by group⟩
    rw [map_mul, map_inv, map_zpow, ← hn', mul_inv_cancel]
  by_contra hno
  push Not at hno
  have hcen : ∀ k ∈ (S : Subgroup Γ), π k = 1 → ∀ w ∈ ρ.range, Commute (ρ k) w := by
    intro k _ hk w hw
    obtain ⟨q₀, hq₀⟩ : ρ k ∈ f.range := hfr ▸ ⟨k, rfl⟩
    obtain ⟨q, hq⟩ : w ∈ f.range := hfr ▸ hw
    have hne : q₀ ^ 2 ≠ QuaternionGroup.a 2 := by
      intro h
      apply hno k (hπ1 k hk)
      rw [← hq₀, ← map_pow, h, hzf]
    show ρ k * w = w * ρ k
    rw [← hq₀, ← hq, ← map_mul, ← map_mul, quat_comm_of_sq_ne q₀ q hne]
  obtain ⟨s, hs, hsu⟩ := hS (f (QuaternionGroup.a 1)) (hmem _)
  obtain ⟨t, ht, htv⟩ := hS (f (QuaternionGroup.xa 0)) (hmem _)
  obtain ⟨k₁, hk₁, hπk₁, n, rfl⟩ := hdec s hs
  obtain ⟨k₂, hk₂, hπk₂, m, rfl⟩ := hdec t ht
  have hc : ∀ j : ℤ, ρ s₀ ^ j ∈ ρ.range := fun j => Subgroup.zpow_mem ρ.range ⟨s₀, rfl⟩ j
  have h12 : Commute (ρ k₁) (ρ k₂) := hcen k₁ hk₁ hπk₁ _ ⟨k₂, rfl⟩
  have h1m : Commute (ρ k₁) (ρ s₀ ^ m) := hcen k₁ hk₁ hπk₁ _ (hc m)
  have h2n : Commute (ρ k₂) (ρ s₀ ^ n) := hcen k₂ hk₂ hπk₂ _ (hc n)
  have hnm : Commute (ρ s₀ ^ n) (ρ s₀ ^ m) := (Commute.refl (ρ s₀)).zpow_zpow n m
  have key : f (QuaternionGroup.a 1) * f (QuaternionGroup.xa 0) =
      f (QuaternionGroup.xa 0) * f (QuaternionGroup.a 1) := by
    rw [← hsu, ← htv]
    simp only [map_mul, map_zpow]
    rw [Commute.mul_mul_mul_comm h2n.symm, Commute.mul_mul_mul_comm h1m.symm, h12.eq, hnm.eq]
  exact quat_noncomm (hfinj (by rw [map_mul, map_mul]; exact key))

theorem mem_inner_of_inverted {X : Type} [Group X] {ι β : MulAut X} (hι : ι ∈ inner X)
    (hβ : β ^ 3 = 1) (h : ι * β * ι⁻¹ = β⁻¹) : β ∈ inner X := by
  have hN : (inner X).Normal := inferInstance
  have h1 : β * ι⁻¹ * β⁻¹ ∈ inner X := hN.conj_mem _ ((inner X).inv_mem hι) β
  have h2 : ι * (β * ι⁻¹ * β⁻¹) ∈ inner X := (inner X).mul_mem hι h1
  have h3 : ι * (β * ι⁻¹ * β⁻¹) = β := by
    calc ι * (β * ι⁻¹ * β⁻¹) = (ι * β * ι⁻¹) * β⁻¹ := by group
      _ = β⁻¹ * β⁻¹ := by rw [h]
      _ = β⁻¹ * β⁻¹ * β ^ 3 := by rw [hβ, mul_one]
      _ = β := by group
  rwa [h3] at h2

end CFSG.RankThree.PartTwo.Late
