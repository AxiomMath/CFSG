module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ASVolI.ChIJK

variable {G : Type} [Group G]

structure IsSplitBNPair (p : ℕ) (B N : Subgroup G) : Prop where
  gen : B ⊔ N = ⊤
  normal_inter : ((B ⊓ N).subgroupOf N).Normal
  coxeter : ∃ S : Set G, (∀ s ∈ S, s ∈ N ∧ s ∉ B ∧ s ^ 2 ∈ B) ∧
    Subgroup.closure S ⊔ (B ⊓ N) = N ∧
    (∀ s ∈ S, ∀ w ∈ N, ∀ b ∈ B, ∃ b₁ ∈ B, ∃ b₂ ∈ B,
      s * b * w = b₁ * w * b₂ ∨ s * b * w = b₁ * (s * w) * b₂) ∧
    (∀ s ∈ S, ∃ b ∈ B, s * b * s ∉ B)
  split : ∃ U : Subgroup G, U ≤ B ∧ (U.subgroupOf B).Normal ∧ IsPGroup p U ∧ ¬ p ∣ U.index ∧
    U ⊓ N = ⊥ ∧ U ⊔ (B ⊓ N) = B ∧ (⨅ n ∈ N, CFSG.conjugate B n) = B ⊓ N

end CFSG.ASVolI.ChIJK
