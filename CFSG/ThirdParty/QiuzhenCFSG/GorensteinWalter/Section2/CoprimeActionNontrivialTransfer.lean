module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- Contrapositive form of Fact 1.1(iv): if a coprime actor acts
nontrivially on a solvable group, it acts nontrivially on every subnormal
self-centralizing subgroup. -/
public theorem commutator_ne_bot_of_subnormal_selfCentralizing_coprime
    {G : Type u} [Group G] [Finite G]
    (Q K K₁ : Subgroup G)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hK1_le_K : K₁ ≤ K)
    (hsub : (K₁.subgroupOf K).IsSubnormal)
    (hself : K ⊓ Subgroup.centralizer (K₁ : Set G) ≤ K₁)
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card K))
    (hsolv : IsSolvable K)
    (hnontriv : ¬ Q ≤ Subgroup.centralizer (K : Set G)) :
    ⁅K₁, Q⁆ ≠ ⊥ := by
  intro hbot
  have hQK₁ : Q ≤ Subgroup.centralizer (K₁ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by
      simpa [Subgroup.commutator_comm] using hbot)
  exact hnontriv
    (centralizes_of_subnormal_selfCentralizing_coprime
      Q K K₁ hQK hK1_le_K hsub hQK₁ hself hcop hsolv)

end CFSG.GorensteinWalter
