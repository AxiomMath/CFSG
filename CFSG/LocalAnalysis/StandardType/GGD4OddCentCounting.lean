module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Datum

variable {G : Type} [Group G] [Finite G]

theorem card_ggAutsOf_eq_card_range_ggBstarAut {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (hperf : commutator K = ⊤) :
    Nat.card ↥(ggAutsOf K Bs hN) = Nat.card ↥(ggBstarAut hN θ).range := by
  have hmap : (ggAutsOf K Bs hN).map (ggInducedAut θ) = (ggBstarAut hN θ).range := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨s, hs, rfl⟩ := (mem_ggAutsOf hN).1 hb
      exact ⟨⟨s, hs⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨K.normalizerMonoidHom ⟨(s : G), hN s.2⟩,
        (mem_ggAutsOf hN).2 ⟨(s : G), s.2, rfl⟩, rfl⟩
  rw [← Subgroup.card_map_of_injective (f := ggInducedAut θ)
    (ggInducedAut_injective_of_perfect hperf θ), hmap]

theorem ggOddCentDatum_of_config {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hm : LargeEvenTwoLocalRank 3 G ≤ 5) {y : G}
    {K : Subgroup G} (hK : GGNbr 3 B x D J y K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hcent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y)
    (hperf : commutator K = ⊤) {lab : LargeEvenLabel} {R : Type} [Group R] {I F : Set (MulAut R)}
    (θ : K ⧸ Subgroup.center K ≃* R) (htag : lab.tag = .D) (hrank : lab.rank = 4)
    (hodd : Odd lab.n) (hAR : GGD4TrialityAutRank I F) (hARI : GGD4TrialityAutRankInn I F)
    (h5 : LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab.n)
    (h4 : LargeEvenTwoLocalRank 3 G = 4 → ∀ (b : G) (hb : b ∈ Bs),
      (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f) →
        ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hout : ¬ ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
      ggLAut K θ ⟨b, hN hb⟩ = u * f) :
    Bs = B ∧ Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ (LargeEvenTwoLocalRank 3 G - 1) ∧
      GGOddCentDatum (ggAutsOf K Bs hN) lab I F θ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBs : IsElemAbelian 3 Bs := hC.2.1.2.1
  have hBBs : B ≤ Bs := hC.2.1.1
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G :=
    hC.1.2.2.2.2.2.2.1.1.2.1
  have hm4le : 4 ≤ LargeEvenTwoLocalRank 3 G := hC.1.2.2.2.2.2.1.2.2.2
  have hm45 : LargeEvenTwoLocalRank 3 G = 4 ∨ LargeEvenTwoLocalRank 3 G = 5 := by omega
  have hyBs : y ∈ Bs := hBBs hK.1.2.1
  have hy1 : y ≠ 1 := hK.1.2.2.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hK.1.2.2.2.1 hk)
  have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
  have hcent_eq : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    le_antisymm hcent (Subgroup.zpowers_le.mpr ⟨hyBs, hyK⟩)
  have hcent_card : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) = 3 := by
    rw [hcent_eq, Nat.card_zpowers, orderOf_eq_prime hy3 hy1]
  rw [not_forall] at hout
  obtain ⟨b₀, hout⟩ := hout
  rw [not_forall] at hout
  obtain ⟨hb₀, hb₀not⟩ := hout
  set Rg : Subgroup (MulAut R) := (ggBstarAut hN θ).range with hRg
  have hRg_ab : IsElemAbelian 3 Rg := by
    rw [hRg]
    exact isElemAbelian_range_ggBstarAut hBs hN θ
  have hmem₀ : ggLAut K θ ⟨b₀, hN hb₀⟩ ∈ Rg := by
    rw [hRg]
    exact ⟨⟨b₀, hb₀⟩, rfl⟩
  have hRg_eq : Nat.card Rg = 3 ^ (LargeEvenTwoLocalRank 3 G - 1) := by
    rcases hm45 with hm4 | hm5
    · have hup : Nat.card Rg ≤ 27 :=
        hARI Rg hRg_ab _ hmem₀ hb₀not (fun a ha hex => by
          obtain ⟨b, rfl⟩ := ha
          exact h4 hm4 (b : G) b.2 hex)
      have hlow : 3 ^ LargeEvenTwoLocalRank 3 G ≤ 3 * Nat.card Rg := by
        rw [hRg]
        exact three_pow_le_card_range_ggBstarAut hC hK hN hperf θ
      rw [hm4] at hlow
      norm_num at hlow
      rw [hm4]
      norm_num
      omega
    · have hup : Nat.card Rg ≤ 81 :=
        hAR Rg hRg_ab _ hmem₀ hb₀not
      have hlow : 3 ^ LargeEvenTwoLocalRank 3 G ≤ 3 * Nat.card Rg := by
        rw [hRg]
        exact three_pow_le_card_range_ggBstarAut hC hK hN hperf θ
      rw [hm5] at hlow
      norm_num at hlow
      rw [hm5]
      norm_num
      omega
  have hA_eq : Nat.card ↥(ggAutsOf K Bs hN) = 3 ^ (LargeEvenTwoLocalRank 3 G - 1) := by
    rw [card_ggAutsOf_eq_card_range_ggBstarAut hN θ hperf, ← hRg]
    exact hRg_eq
  have hcardBs : Nat.card Bs = 3 ^ LargeEvenTwoLocalRank 3 G := by
    have h1 := card_ggAutsOf_mul_card (X := K) (S := Bs) hN
    rw [hcent_card, hA_eq] at h1
    rw [← h1, mul_comm, ← pow_succ']
    congr 1
    omega
  have hBs_eq_B : Bs = B := by
    have hle : Nat.card Bs ≤ Nat.card B := by rw [hcardBs, hBc]
    exact (Subgroup.eq_of_le_of_card_ge hBBs hle).symm
  refine ⟨hBs_eq_B, hA_eq, htag, hrank, hodd, ?_, ?_, ?_⟩
  · intro hA4
    have hm5 : LargeEvenTwoLocalRank 3 G = 5 := by
      rcases hm45 with h4' | h5'
      · exfalso
        rw [h4'] at hA_eq
        norm_num at hA_eq hA4
        omega
      · exact h5'
    exact h5 hm5
  · intro hA3 a ha hinn
    have hm4 : LargeEvenTwoLocalRank 3 G = 4 := by
      rcases hm45 with h4' | h5'
      · exact h4'
      · exfalso
        rw [h5'] at hA_eq
        norm_num at hA_eq hA3
        omega
    obtain ⟨b, hb, rfl⟩ := (mem_ggAutsOf hN).1 ha
    exact h4 hm4 b hb hinn
  · exact ⟨K.normalizerMonoidHom ⟨b₀, hN hb₀⟩,
      (mem_ggAutsOf hN).2 ⟨b₀, hb₀, rfl⟩, hb₀not⟩

end Datum

end CFSG.StandardType
