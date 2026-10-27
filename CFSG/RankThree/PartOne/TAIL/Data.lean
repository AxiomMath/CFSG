module

public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

structure KData (G : Type) [Group G] [Finite G] (K : Subgroup G) (c : G) : Prop where
  inf_centralizer : K ⊓ Subgroup.centralizer (K : Set G) = ⊥
  rank_one : CFSG.pRank 7 ↥K ≤ 1
  sylow : ∀ R : Subgroup G, R ≤ K → IsPGroup 7 R → IsCyclic ↥R ∧ Nat.card ↥R ≤ 49
  out_index : ∀ R : Subgroup G, IsPGroup 7 R → R ≤ Subgroup.normalizer (K : Set G) →
    (R ⊓ (K ⊔ Subgroup.centralizer (K : Set G))).relIndex R ≤ 7
  out_central : ∀ n ∈ Subgroup.normalizer (K : Set G), n * c * n⁻¹ ∈ Subgroup.zpowers c →
    n * c * n⁻¹ = c

structure LData (G : Type) [Group G] [Finite G] (L B : Subgroup G) : Prop where
  sylow : B ≤ L ∧ IsPGroup 7 B ∧ ¬ 7 ∣ B.relIndex L
  out_seven : ∀ x ∈ Subgroup.normalizer (L : Set G), (∃ k : ℕ, orderOf x = 7 ^ k) →
    x ∈ L ⊔ Subgroup.centralizer (L : Set G)
  irreducible : ∀ d ∈ B, d ≠ 1 →
    ∃ g ∈ L ⊓ Subgroup.normalizer (B : Set G), g * d * g⁻¹ ∉ Subgroup.zpowers d
  aut_pm : ∀ n ∈ Subgroup.normalizer (L : Set G), n ∈ Subgroup.normalizer (B : Set G) →
    ∃ l ∈ L ⊓ Subgroup.normalizer (B : Set G),
      (∀ x ∈ B, (l * n) * x * (l * n)⁻¹ = x) ∨ (∀ x ∈ B, (l * n) * x * (l * n)⁻¹ = x⁻¹)

end CFSG.RankThree.PartOne.TAIL
