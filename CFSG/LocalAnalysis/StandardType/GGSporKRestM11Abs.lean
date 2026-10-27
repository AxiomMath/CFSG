module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestFStarSylow

public section

namespace CFSG.StandardType.SporadicShape

private theorem factorization_three_7920 : (7920 : ℕ).factorization 3 = 2 := by
  rw [show (7920 : ℕ) = 3 ^ 2 * 880 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

private theorem factorization_three_144 : (144 : ℕ).factorization 3 = 2 := by
  rw [show (144 : ℕ) = 3 ^ 2 * 16 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem sporKRest_exists_sylow_of_normalizer {G : Type} [Group G] [Finite G] (S N : Subgroup G)
    (hG : Nat.card G = 7920) (hS : Nat.card S = 9) (hN : Nat.card N = 144)
    (hnorm : Subgroup.normalizer (S : Set G) = N)
    (hcent : ∀ t ∈ N, (∀ s ∈ S, t * s = s * t) → t ∈ S)
    (hmax : ∀ Y : Subgroup G, N ≤ Y → Y = N ∨ Y = ⊤) :
    ∃ S₀ : Sylow 3 G,
      (∀ Y : Subgroup G, Subgroup.normalizer ((S₀ : Subgroup G) : Set G) ≤ Y →
        Y = Subgroup.normalizer ((S₀ : Subgroup G) : Set G) ∨ Y = ⊤) ∧
      IsPGroup 3 ↥(CFSG.generalizedFitting ↥(Subgroup.normalizer ((S₀ : Subgroup G) : Set G))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hScard : Nat.card ↥S = 3 ^ (Nat.card G).factorization 3 := by
    rw [hS, hG, factorization_three_7920]
    norm_num
  let S₀ : Sylow 3 G := Sylow.ofCard S hScard
  have hS₀ : (S₀ : Subgroup G) = S := Sylow.coe_ofCard S hScard
  refine ⟨S₀, ?_, ?_⟩
  · intro Y hY
    have hY' : N ≤ Y := by rwa [hS₀, hnorm] at hY
    simpa only [hS₀, hnorm] using hmax Y hY'
  · rw [hS₀, hnorm]
    have hle : S ≤ N := by
      rw [← hnorm]
      exact Subgroup.le_normalizer
    have hSsub : Nat.card ↥(S.subgroupOf N) = 9 := by
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans hS
    have hS'scard : Nat.card ↥(S.subgroupOf N) = 3 ^ (Nat.card ↥N).factorization 3 := by
      rw [hSsub, hN, factorization_three_144]
      norm_num
    let S' : Sylow 3 ↥N := Sylow.ofCard (S.subgroupOf N) hS'scard
    have hS'coe : (S' : Subgroup ↥N) = S.subgroupOf N := Sylow.coe_ofCard _ hS'scard
    have hS'normal : (S' : Subgroup ↥N).Normal := by
      rw [hS'coe, ← hnorm]
      exact Subgroup.normal_in_normalizer
    haveI : (S' : Subgroup ↥N).Normal := hS'normal
    have hS'card : Nat.card ↥(S' : Subgroup ↥N) = 9 := by
      rw [hS'coe]
      exact hSsub
    have hS'solv : Group.IsSolvable ↥S' := by
      haveI : Group.IsNilpotent ↥S' := IsPGroup.isNilpotent (Sylow.isPGroup' S')
      exact IsNilpotent.to_isSolvable
    have hQcard : Nat.card (↥N ⧸ (S' : Subgroup ↥N)) = 2 ^ 4 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (S' : Subgroup ↥N)
      rw [hN, hS'card] at h
      omega
    have hQsolv : Group.IsSolvable (↥N ⧸ (S' : Subgroup ↥N)) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Group.IsNilpotent (↥N ⧸ (S' : Subgroup ↥N)) :=
        IsPGroup.isNilpotent (IsPGroup.of_card (p := 2) (n := 4) hQcard)
      exact IsNilpotent.to_isSolvable
    have hNsolv : Group.IsSolvable ↥N := by
      haveI : Group.IsSolvable ↥(S' : Subgroup ↥N) := hS'solv
      haveI : Group.IsSolvable (↥N ⧸ (S' : Subgroup ↥N)) := hQsolv
      exact Group.isSolvable_of_subgroup_quotient (S' : Subgroup ↥N)
    have hC : Subgroup.centralizer ((S' : Subgroup ↥N) : Set ↥N) ≤ (S' : Subgroup ↥N) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff] at ht
      rw [hS'coe, Subgroup.mem_subgroupOf]
      apply hcent (t : G) t.2
      intro s hs
      have hmem : (⟨s, hle hs⟩ : ↥N) ∈ (S' : Subgroup ↥N) := by
        rw [hS'coe, Subgroup.mem_subgroupOf]
        exact hs
      simpa using (congrArg Subtype.val (ht ⟨s, hle hs⟩ hmem)).symm
    exact sporKRest_fstar_isPGroup_of_normal_sylow hNsolv S' hS'normal hC

end CFSG.StandardType.SporadicShape
