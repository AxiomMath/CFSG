module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.Shult

open CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] def IsOmegaOne (V P : Subgroup G) : Prop :=
  V ≤ P ∧ ∀ x ∈ P, x ^ 2 = 1 → x ∈ V

@[expose] def IsBenderHull (L : Subgroup G) : Prop :=
  IsQuasisimple L ∧ Subgroup.center L = fusionOddCore L ∧
    fusionIsBenderGroup (↥L ⧸ Subgroup.center ↥L)

@[expose] def ShultCoreConclusion (T V : Subgroup G) : Prop :=
  (Nat.card V = 2 ∧ Subgroup.normalClosure (V : Set G) = oddCoreIn (Subgroup.normalClosure
      (V : Set G)) ⊔ V) ∨
  (4 ≤ Nat.card V ∧ IsBenderHull (Subgroup.normalClosure (V : Set G)) ∧
    IsOmegaOne V (T ⊓ Subgroup.normalClosure (V : Set G)))

@[expose] def IsBenderQuasisimple (L : Subgroup G) (f : ℕ) : Prop :=
  IsQuasisimple L ∧ Subgroup.center L = fusionOddCore L ∧
    ((2 ≤ f ∧ Nonempty (↥L ⧸ Subgroup.center ↥L ≃* PSL(2, GaloisField 2 f))) ∨
      (2 ≤ f ∧ Nonempty (↥L ⧸ Subgroup.center ↥L ≃* PSU3 2 f)) ∨
      (∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ Nonempty (↥L ⧸ Subgroup.center ↥L ≃* Sz a)))

@[expose] def ShultConclusion (T V : Subgroup G) : Prop :=
  (Nat.card V = 2 ∧ Subgroup.normalClosure (V : Set G) = oddCoreIn (Subgroup.normalClosure
      (V : Set G)) ⊔ V) ∨
  ∃ f : ℕ, Nat.card V = 2 ^ f ∧ IsBenderQuasisimple (Subgroup.normalClosure (V : Set G)) f ∧
    IsOmegaOne V (T ⊓ Subgroup.normalClosure (V : Set G))

@[expose] def ShultFixedPoint (M V : Subgroup G) : Prop :=
  ∀ v ∈ V, v ≠ 1 → ∃! c : G ⧸ M, v • c = c

@[expose] def ShultI85Hyp (M V : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ V ≠ ⊥ ∧ V ≤ M ∧ (V.subgroupOf M).Normal ∧ IsElemAbelian 2 V ∧ ShultFixedPoint M V

@[expose] def ShultI85Part1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G), ShultI85Hyp M V →
    (Nat.card V = 2 ∧ Subgroup.normalClosure (V : Set G) = oddCoreIn (Subgroup.normalClosure
      (V : Set G)) ⊔ V) ∨
    ∃ f : ℕ, Nat.card V = 2 ^ f ∧ IsBenderQuasisimple (Subgroup.normalClosure (V : Set G)) f ∧
      (∃ P : Subgroup G, IsSylowTwoOf P (Subgroup.normalClosure (V : Set G)) ∧ IsOmegaOne V P) ∧
      M ⊓ Subgroup.normalClosure (V : Set G) =
        Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalClosure (V : Set G) ∧
      fusionStronglyEmbedded ((M ⊓ Subgroup.normalClosure (V : Set G)).subgroupOf
        (Subgroup.normalClosure (V : Set G)))

@[expose] def ShultI85Part2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G), ShultI85Hyp M V →
    ∀ [((Subgroup.centralizer (V : Set G)).subgroupOf M).Normal],
      Group.IsSolvable (↥M ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf M)

theorem IsBenderQuasisimple.isBenderHull {L : Subgroup G} {f : ℕ} (h : IsBenderQuasisimple L f) :
    IsBenderHull L := by
  refine ⟨h.1, h.2.1, ?_⟩
  rcases h.2.2 with ⟨hf, e⟩ | ⟨hf, e⟩ | ⟨a, ha, -, e⟩
  · exact Or.inl ⟨f, hf, e⟩
  · exact Or.inr (Or.inl ⟨f, hf, e⟩)
  · exact Or.inr (Or.inr ⟨a, ha, e⟩)

end CFSG.Quasithin.Shult
