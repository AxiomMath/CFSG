module

public import Mathlib.GroupTheory.Sylow
import CFSG.Quasithin.EmptyFaithful.S146zXGIndex
import CFSG.GroupTheory.PermutingProducts
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Permutable

public section

namespace CFSG.GroupTheory.PermSylowTwo

open Subgroup
open scoped Pointwise

theorem eq_bot_of_permutes_sylow_two_of_odd_of_not_three_dvd_of_card_168
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hG : Nat.card G = 168)
    (S : Sylow 2 G) (B : Subgroup G) (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hperm : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G)) : B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card S = 8 := by
    rw [Sylow.card_eq_multiplicity, hG]
    decide +kernel
  have hBd : Nat.card B ∣ 168 := hG ▸ B.card_subgroup_dvd_card
  have hB24 : Nat.Coprime (Nat.card B) 24 := by
    have hB8 : Nat.Coprime (Nat.card B) 8 := by
      simpa using hBo.coprime_two_right.pow_right 3
    have hBthree : Nat.Coprime (Nat.card B) 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hB3).symm
    simpa using hB8.mul_right hBthree
  have hB7 : Nat.card B ∣ 7 := hB24.dvd_of_dvd_mul_left (by simpa using hBd)
  rcases (Nat.dvd_prime Nat.prime_seven).mp hB7 with hB | hB
  · exact Subgroup.card_eq_one.mp hB
  have hBS : B ⊓ (S : Subgroup G) = ⊥ := Subgroup.disjoint_of_coprime_natCard (by
    rw [hS]
    simpa using hBo.coprime_two_right.pow_right 3) |>.eq_bot
  have hcard : Nat.card (B ⊔ (S : Subgroup G) : Subgroup G) = 56 := by
    rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hperm hBS, hB, hS]
  have hmul := (B ⊔ (S : Subgroup G)).card_mul_index
  rw [hcard, hG] at hmul
  have hidx : (B ⊔ (S : Subgroup G)).index = 3 := by omega
  have hle := CFSG.Quasithin.S146zX.card_le_six_of_index_three _ hidx
  omega

theorem eq_bot_of_permutes_sylow_two_of_odd_of_not_three_dvd_of_quotient_card_168
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : Nat.card Q = 168) (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (e : G ⧸ N ≃* Q) (S : Sylow 2 G) (B : Subgroup G)
    (hBo : Odd (Nat.card B)) (hB3 : ¬ 3 ∣ Nat.card B)
    (hperm : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G)) : B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : G →* Q := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hmap : B.map φ = ⊥ :=
    eq_bot_of_permutes_sylow_two_of_odd_of_not_three_dvd_of_card_168 hQ
      (S.mapSurjective hφ) (B.map φ) (Odd.of_dvd_nat hBo (Subgroup.card_map_dvd B φ))
      (fun h => hB3 (h.trans (Subgroup.card_map_dvd B φ)))
      (CFSG.GroupTheory.map_permutes_map φ hperm)
  have hBN : B ≤ N := by
    intro b hb
    have hb1 : φ b = 1 := by
      have hbmap := Subgroup.mem_map_of_mem φ hb
      rwa [hmap, Subgroup.mem_bot] at hbmap
    have hbq : (QuotientGroup.mk' N) b = 1 := by
      apply e.injective
      simpa [φ] using hb1
    have hbker : b ∈ (QuotientGroup.mk' N).ker := hbq
    rwa [QuotientGroup.ker_mk'] at hbker
  obtain ⟨j, hj⟩ := hN.exists_card_eq
  have hd : Disjoint B N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hj]
    exact hBo.coprime_two_right.pow_right j)
  simpa only [inf_of_le_left hBN] using hd.eq_bot

end CFSG.GroupTheory.PermSylowTwo
