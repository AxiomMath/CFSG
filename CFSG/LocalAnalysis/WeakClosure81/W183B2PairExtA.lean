module

import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddCount
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem w183b2_pq_inf_left {P Q M₁ M₂ K : Subgroup G} (hQ : Q ≤ M₂)
    (hK : (K : Set G) = ((Q ⊓ M₁ : Subgroup G) : Set G) * ((P ⊓ M₂ : Subgroup G) : Set G)) :
    P ⊓ K = P ⊓ M₂ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxP, hxK⟩ := hx
    rw [Subgroup.mem_inf]
    refine ⟨hxP, ?_⟩
    have hxK' : x ∈ (K : Set G) := hxK
    rw [hK, Set.mem_mul] at hxK'
    obtain ⟨q, hq, p, hp, hqp⟩ := hxK'
    have hq' : q ∈ (Q ⊓ M₁ : Subgroup G) := hq
    have hp' : p ∈ (P ⊓ M₂ : Subgroup G) := hp
    rw [Subgroup.mem_inf] at hq' hp'
    rw [← hqp]
    exact M₂.mul_mem (hQ hq'.1) hp'.2
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxP, hxM₂⟩ := hx
    rw [Subgroup.mem_inf]
    refine ⟨hxP, ?_⟩
    change x ∈ (K : Set G)
    rw [hK, Set.mem_mul]
    have h1A : (1 : G) ∈ (Q ⊓ M₁ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨Q.one_mem, M₁.one_mem⟩
    have hxT : x ∈ (P ⊓ M₂ : Subgroup G) := Subgroup.mem_inf.mpr ⟨hxP, hxM₂⟩
    exact ⟨1, h1A, x, hxT, one_mul x⟩

theorem w183b2_pq_inf_right {P Q M₁ M₂ K : Subgroup G} (hP : P ≤ M₁)
    (hK : (K : Set G) = ((Q ⊓ M₁ : Subgroup G) : Set G) * ((P ⊓ M₂ : Subgroup G) : Set G)) :
    Q ⊓ K = Q ⊓ M₁ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxQ, hxK⟩ := hx
    rw [Subgroup.mem_inf]
    refine ⟨hxQ, ?_⟩
    have hxK' : x ∈ (K : Set G) := hxK
    rw [hK, Set.mem_mul] at hxK'
    obtain ⟨q, hq, p, hp, hqp⟩ := hxK'
    have hq' : q ∈ (Q ⊓ M₁ : Subgroup G) := hq
    have hp' : p ∈ (P ⊓ M₂ : Subgroup G) := hp
    rw [Subgroup.mem_inf] at hq' hp'
    rw [← hqp]
    exact M₁.mul_mem hq'.2 (hP hp'.1)
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxQ, hxM₁⟩ := hx
    rw [Subgroup.mem_inf]
    refine ⟨hxQ, ?_⟩
    change x ∈ (K : Set G)
    rw [hK, Set.mem_mul]
    have hxA : x ∈ (Q ⊓ M₁ : Subgroup G) := Subgroup.mem_inf.mpr ⟨hxQ, hxM₁⟩
    have h1T : (1 : G) ∈ (P ⊓ M₂ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨P.one_mem, M₂.one_mem⟩
    exact ⟨x, hxA, 1, h1T, mul_one x⟩

theorem w183b2_pq_isPGroup {P Q M₁ M₂ K : Subgroup G} (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hK : (K : Set G) = ((Q ⊓ M₁ : Subgroup G) : Set G) * ((P ⊓ M₂ : Subgroup G) : Set G)) :
    IsPGroup 2 K := by
  have hleA : (Q ⊓ M₁ : Subgroup G) ≤ K := by
    intro x hx
    change x ∈ (K : Set G)
    rw [hK, Set.mem_mul]
    have h1T : (1 : G) ∈ (P ⊓ M₂ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨P.one_mem, M₂.one_mem⟩
    exact ⟨x, hx, 1, h1T, mul_one x⟩
  have hleT : (P ⊓ M₂ : Subgroup G) ≤ K := by
    intro x hx
    change x ∈ (K : Set G)
    rw [hK, Set.mem_mul]
    have h1A : (1 : G) ∈ (Q ⊓ M₁ : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨Q.one_mem, M₁.one_mem⟩
    exact ⟨1, h1A, x, hx, one_mul x⟩
  have hcov : ∀ b ∈ K, ∃ a ∈ (Q ⊓ M₁ : Subgroup G), ∃ t ∈ (P ⊓ M₂ : Subgroup G), b = a * t := by
    intro b hb
    have hb' : b ∈ (K : Set G) := hb
    rw [hK, Set.mem_mul] at hb'
    obtain ⟨a, ha, t, ht, hat⟩ := hb'
    exact ⟨a, ha, t, ht, hat.symm⟩
  have hprod := CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.card_mul_inf_eq
    (Q ⊓ M₁) (P ⊓ M₂) K hleA hleT hcov
  have hA : IsPGroup 2 (Q ⊓ M₁ : Subgroup G) := hQ.to_le inf_le_left
  have hT : IsPGroup 2 (P ⊓ M₂ : Subgroup G) := hP.to_le inf_le_left
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨b, hb⟩ := hT.exists_card_eq
  refine IsPGroup.of_card_dvd_pow (n := a + b)
    ⟨Nat.card (((Q ⊓ M₁ : Subgroup G) ⊓ (P ⊓ M₂ : Subgroup G)) : Subgroup G), ?_⟩
  rw [hprod, ha, hb, ← pow_add]

end CFSG.LocalAnalysis.WeakClosure81

end
