module

public import CFSG.GroupTheory.PermSylowTwo.Sym
import CFSG.GroupTheory.PermutingProducts
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Permutable

public section

namespace CFSG.GroupTheory.PermSylowTwo

open Equiv CFSG.QuasithinUnique
open scoped Pointwise

theorem eq_bot_of_permutes_sylow_two_of_odd_of_not_three_dvd (α : Type) [Finite α]
    {S B : Subgroup (Perm α)} (hS : IsSylowTwoOf S ⊤) (hBo : Odd (Nat.card B))
    (hB3 : ¬ 3 ∣ Nat.card B)
    (hperm : (B : Set (Perm α)) * (S : Set (Perm α)) =
      (S : Set (Perm α)) * (B : Set (Perm α))) : B = ⊥ := by
  classical
  let _ := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have hBS : B ⊓ S = ⊥ := by
    apply Disjoint.eq_bot
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hk]
    exact hBo.coprime_two_right.pow_right k
  have hcard := CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hperm hBS
  have h3 : ¬ 3 ∣ Nat.card (B ⊔ S : Subgroup (Perm α)) := by
    rw [hcard]
    exact Nat.prime_three.not_dvd_mul hB3 (not_three_dvd_card_of_isPGroup_two hS.2.1)
  have hY2 := isPGroup_two_of_sylow_le α hS le_sup_right (Or.inl h3)
  obtain ⟨j, hj⟩ := hY2.exists_card_eq
  have hd : Disjoint B (B ⊔ S) := Subgroup.disjoint_of_coprime_natCard (by
    rw [hj]
    exact hBo.coprime_two_right.pow_right j)
  simpa only [inf_of_le_left (show B ≤ B ⊔ S from le_sup_left)] using hd.eq_bot

theorem eq_bot_of_permutes_sylow_two_of_odd_of_not_three_dvd_of_quotient_perm
    {G : Type} [Group G] [Finite G] (α : Type) [Finite α]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) (e : G ⧸ N ≃* Perm α)
    (S : Sylow 2 G) (B : Subgroup G) (hBo : Odd (Nat.card B))
    (hB3 : ¬ 3 ∣ Nat.card B)
    (hperm : (B : Set G) * (S : Set G) = (S : Set G) * (B : Set G)) : B = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : G →* Perm α := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective N)
  let S' : Sylow 2 (Perm α) := S.mapSurjective hφ
  have hS' : IsSylowTwoOf (S' : Subgroup (Perm α)) ⊤ := by
    refine ⟨le_top, S'.isPGroup', ?_⟩
    change ¬ 2 ∣ (S' : Subgroup (Perm α)).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact S'.not_dvd_index
  have hmap : B.map φ = ⊥ := by
    refine eq_bot_of_permutes_sylow_two_of_odd_of_not_three_dvd α hS'
      (Odd.of_dvd_nat hBo (Subgroup.card_map_dvd B φ))
      (fun h => hB3 (h.trans (Subgroup.card_map_dvd B φ))) ?_
    simpa only [S', Sylow.coe_mapSurjective] using CFSG.GroupTheory.map_permutes_map φ hperm
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
