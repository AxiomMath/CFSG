module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerCosets
public import CFSG.Assembly.Defs

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ShultStronglyClosedTI

universe u

variable {G : Type u} [Group G]

@[expose] def baseOrbit (H N : Subgroup G) : Set (rightCosetSpace H) :=
  {omega | ∃ g ∈ N, rightCosetTranslate H (rightCosetMk H 1) g = omega}

theorem range_restrictedRightCosetEmbedding (H N : Subgroup G) :
    Set.range (restrictedRightCosetEmbedding H N) = baseOrbit H N := by
  rw [restrictedRightCosetEmbedding_range]
  ext omega
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, n.2, (pointRightCosetMul_eq_translate H _ _).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, pointRightCosetMul_eq_translate H _ _⟩

theorem restrictedRightCosetEmbedding_base (H N : Subgroup G) :
    restrictedRightCosetEmbedding H N (rightCosetMk (H.subgroupOf N) 1) = rightCosetMk H 1 :=
  rfl

theorem restrictedRightCosetEmbedding_translate (H N : Subgroup G)
    (a : rightCosetSpace (H.subgroupOf N)) (n : N) :
    restrictedRightCosetEmbedding H N (rightCosetTranslate (H.subgroupOf N) a n) =
      rightCosetTranslate H (restrictedRightCosetEmbedding H N a) (n : G) := by
  rw [← pointRightCosetMul_eq_translate, ← pointRightCosetMul_eq_translate,
    restrictedRightCosetEmbedding_equivariant]

theorem restricted_stabilizer_map (H N : Subgroup G) (lam : rightCosetSpace (H.subgroupOf N)) :
    (rightCosetStabilizer (H.subgroupOf N) lam).map N.subtype =
      N ⊓ rightCosetStabilizer H (restrictedRightCosetEmbedding H N lam) := by
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn' : rightCosetTranslate (H.subgroupOf N) lam n = lam :=
      (mem_rightCosetStabilizer_iff _ _ _).mp hn
    refine ⟨n.2, (mem_rightCosetStabilizer_iff _ _ _).mpr ?_⟩
    change rightCosetTranslate H _ (n : G) = _
    rw [← restrictedRightCosetEmbedding_translate, hn']
  · rintro ⟨hgN, hg⟩
    have hg' := (mem_rightCosetStabilizer_iff _ _ _).mp hg
    refine ⟨⟨g, hgN⟩, (mem_rightCosetStabilizer_iff _ _ _).mpr ?_, rfl⟩
    apply restrictedRightCosetEmbedding_injective H N
    rw [restrictedRightCosetEmbedding_translate]
    exact hg'

theorem card_restricted_stabilizer (H N : Subgroup G) (lam : rightCosetSpace (H.subgroupOf N)) :
    Nat.card (rightCosetStabilizer (H.subgroupOf N) lam) =
      Nat.card (N ⊓ rightCosetStabilizer H (restrictedRightCosetEmbedding H N lam) :
        Subgroup G) := by
  rw [← restricted_stabilizer_map, Subgroup.card_map_of_injective N.subtype_injective]

theorem restricted_mem_pointFixedSet_iff (H N : Subgroup G) (T : Subgroup N)
    (lam : rightCosetSpace (H.subgroupOf N)) :
    lam ∈ pointFixedSet (H.subgroupOf N) T ↔
      restrictedRightCosetEmbedding H N lam ∈ pointFixedSet H (T.map N.subtype) := by
  rw [mem_pointFixedSet_iff, mem_pointFixedSet_iff, ← Subgroup.map_le_map_iff_of_injective
    N.subtype_injective, restricted_stabilizer_map]
  exact ⟨fun h => h.trans inf_le_right,
    fun h => le_inf (Subgroup.map_subtype_le T) h⟩

theorem image_conjugacyWithin_subgroupOf (H N : Subgroup G) (r : N) :
    N.subtype '' conjugacyWithin (H.subgroupOf N) r = conjugacyWithin (H ⊓ N) (r : G) := by
  apply Set.Subset.antisymm
  · rintro x ⟨w, ⟨k, hk⟩, rfl⟩
    exact ⟨⟨(k : N), k.2, (k : N).2⟩, congrArg (fun a : N => (a : G)) hk⟩
  · rintro x ⟨k, hk⟩
    let kN : N := ⟨k, k.2.2⟩
    refine ⟨kN⁻¹ * r * kN, ⟨⟨kN, k.2.1⟩, rfl⟩, ?_⟩
    exact hk

theorem card_conjugacyWithin_subgroupOf (H N : Subgroup G) (r : N) :
    Nat.card (conjugacyWithin (H.subgroupOf N) r) =
      Nat.card (conjugacyWithin (H ⊓ N) (r : G)) := by
  rw [← image_conjugacyWithin_subgroupOf, Nat.card_image_of_injective N.subtype_injective]

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
