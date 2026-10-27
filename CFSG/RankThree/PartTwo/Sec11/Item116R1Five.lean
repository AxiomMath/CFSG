module

public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJCases
public import CFSG.RankThree.PartTwo.Sec11.Item116R1Alg
public import CFSG.RankThree.PartTwo.Sec11.Item116R1E1
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps345.Sylow

public section

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem hloc_of_localRank {G : Type*} [Group G] [Finite G]
    (hl : ∀ r : ℕ, r.Prime → 3 < r → CFSG.Assembly.RankThreeEven.localRank r G < 3) :
    ∀ r : ℕ, r.Prime → 3 < r → ∀ Q : Subgroup G, IsPGroup r Q → ∀ u : G, u ≠ 1 →
      IsPGroup 2 (Subgroup.zpowers u) → CFSG.pRank r ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2 := by
  intro r hr hr3 Q _hQ u hu hT2
  have hT : Subgroup.zpowers u ≠ ⊥ := fun h => hu (Subgroup.zpowers_eq_bot.mp h)
  have hH : Q ⊓ Subgroup.centralizer {u} ≤
      Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer {u} := (Subgroup.mem_inf.mp hx).2
    have hC : x ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hxC
    exact Subgroup.centralizer_le_normalizer _ hC
  have key := CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ.pRank_le_localRank_of_le_normalizer
    hr hT hT2 hH
  have hlt := hl r hr hr3
  omega

end CFSG.RankThree.PartTwo.Sec11

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

theorem five_dvd_card_quotient {G : Type*} [Group G] [Finite G]
    (hloc : ∀ r : ℕ, r.Prime → 3 < r → ∀ Q : Subgroup G, IsPGroup r Q → ∀ u : G, u ≠ 1 →
      IsPGroup 2 (Subgroup.zpowers u) → CFSG.pRank r ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2)
    {θ H S K' : Subgroup G} [(θ.subgroupOf K').Normal]
    (hθH : θ ≤ H) (hHθ : H ≤ Subgroup.normalizer (θ : Set G)) (hθs : Group.IsSolvable θ)
    (hθ3 : ¬ 3 ∣ Nat.card θ) (hO2 : inSubgroup (CFSG.pCore 2) θ = ⊥) (hSθ : S ≤ θ)
    (hS2 : IsPGroup 2 S) (hK'H : K' ≤ H) (hK'S : K' ≤ Subgroup.normalizer (S : Set G))
    (hperf : ⁅K', K'⁆ = K') (hsimp : IsSimpleGroup (K' ⧸ θ.subgroupOf K'))
    (hnt : ∃ k ∈ K', ∃ s ∈ S, k * s * k⁻¹ ≠ s) : 5 ∣ Nat.card (K' ⧸ θ.subgroupOf K') := by
  have hperfK : ⁅(⊤ : Subgroup K'), (⊤ : Subgroup K')⁆ = ⊤ := pel_perfect_top hperf
  have hperfQ : ⁅(⊤ : Subgroup (K' ⧸ θ.subgroupOf K')), (⊤ : Subgroup (K' ⧸ θ.subgroupOf K'))⁆ = ⊤ := by
    have h1 : Subgroup.map (QuotientGroup.mk' (θ.subgroupOf K')) ⁅(⊤ : Subgroup K'), (⊤ : Subgroup K')⁆ = ⊤ := by
      rw [hperfK, Subgroup.map_top_of_surjective (QuotientGroup.mk' (θ.subgroupOf K'))
        (QuotientGroup.mk'_surjective (θ.subgroupOf K'))]
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective (QuotientGroup.mk' (θ.subgroupOf K'))
      (QuotientGroup.mk'_surjective (θ.subgroupOf K'))] at h1
    exact h1
  obtain ⟨r, hr, hr5, hrQ⟩ : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card (K' ⧸ θ.subgroupOf K') := by
    by_contra hcon
    have hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (⊤ : Subgroup (K' ⧸ θ.subgroupOf K')) →
        ℓ = 2 ∨ ℓ = 3 := by
      intro ℓ hℓ hdvd
      rw [Subgroup.card_top] at hdvd
      have hlt : ℓ < 5 := by
        by_contra h5
        exact hcon ⟨ℓ, hℓ, by omega, hdvd⟩
      interval_cases ℓ
      all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hℓ (by norm_num)
    haveI hsolv : Group.IsSolvable (⊤ : Subgroup (K' ⧸ θ.subgroupOf K')) :=
      CFSG.SignalizerFunctorTheorem.Glauberman.isSolvable_of_prime_support
        Nat.prime_two Nat.prime_three (by norm_num) hsupp
    obtain ⟨d, hd⟩ := exists_ne (1 : K' ⧸ θ.subgroupOf K')
    have hd1 := pel_eq_one_of_solvable_perfect (D := ↥(⊤ : Subgroup (K' ⧸ θ.subgroupOf K')))
      (pel_perfect_top hperfQ) ⟨d, Subgroup.mem_top d⟩
    exact hd (congrArg Subtype.val hd1)
  have hr3 : 3 < r := by omega
  have hexists : ∃ x ∈ K', IsPGroup r (Subgroup.zpowers x) ∧ ∃ s ∈ S, x * s * x⁻¹ ≠ s := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk, s, hs, hks⟩ := hnt
    exact hks (centralizes_of_pElements hperf hK'S hθs hsimp hr hrQ hcon k hk s hs)
  obtain ⟨x, hxK, hxq, s, hs, hxs⟩ := hexists
  have hxθ : x ∈ Subgroup.normalizer (θ : Set G) := hHθ (hK'H hxK)
  have hxS : x ∈ Subgroup.normalizer (S : Set G) := hK'S hxK
  have hxS1 : ⁅S, Subgroup.zpowers x⁆ ≠ ⊥ := by
    intro hbot
    apply hxs
    have h1 : ⁅s, x⁆ ∈ ⁅S, Subgroup.zpowers x⁆ :=
      Subgroup.commutator_mem_commutator hs (Subgroup.mem_zpowers x)
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : s * x = x * s := commutatorElement_eq_one_iff_mul_comm.mp h1
    rw [← h2, mul_inv_cancel_right]
  have hr5' : r = 5 := e1_core hloc hθs hθ3 hO2 hS2 hSθ hr hr3 hxq hxθ hxS hxS1
  rw [hr5'] at hrQ
  exact hrQ

end CFSG.RankThree.PartTwo.Sec11

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

@[expose] def FiveCaseCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ r : ℕ, r.Prime → 3 < r → ∀ Q : Subgroup G, IsPGroup r Q → ∀ u : G, u ≠ 1 →
      IsPGroup 2 (Subgroup.zpowers u) → CFSG.pRank r ↥(Q ⊓ Subgroup.centralizer {u}) ≤ 2) →
    ∀ (θ H S K₁ K₂ : Subgroup G) [(θ.subgroupOf K₁).Normal] [(θ.subgroupOf K₂).Normal],
      θ ≤ H → H ≤ Subgroup.normalizer (θ : Set G) → Group.IsSolvable θ → ¬ 3 ∣ Nat.card θ →
      inSubgroup (CFSG.pCore 2) θ = ⊥ → S ≤ θ → IsPGroup 2 S → ¬ 2 ∣ S.relIndex θ →
      K₁ ≤ H → K₁ ≤ Subgroup.normalizer (S : Set G) → ⁅K₁, K₁⁆ = K₁ →
      K₂ ≤ H → K₂ ≤ Subgroup.normalizer (S : Set G) → ⁅K₂, K₂⁆ = K₂ →
      ⁅K₁, K₂⁆ ≤ θ → (K₁ ⊔ θ) ⊓ (K₂ ⊔ θ) = θ →
      IsSimpleGroup (K₁ ⧸ θ.subgroupOf K₁) → 5 ∣ Nat.card (K₁ ⧸ θ.subgroupOf K₁) →
      IsSimpleGroup (K₂ ⧸ θ.subgroupOf K₂) → 5 ∣ Nat.card (K₂ ⧸ θ.subgroupOf K₂) →
      (∃ k ∈ K₁, ∃ s ∈ S, k * s * k⁻¹ ≠ s) → (∃ k ∈ K₂, ∃ s ∈ S, k * s * k⁻¹ ≠ s) → False

end CFSG.RankThree.PartTwo.Sec11
