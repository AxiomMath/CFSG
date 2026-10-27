module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

namespace CFSG
end CFSG
open CFSG

/-- An extraspecial `p`-group has center of order `p`, elementary abelian central quotient, and
nontrivial central quotient. -/
public class CFSG.IsExtraspecial (p : ℕ) (G : Type*) [Group G] : Prop where
  center_order_p (p) (G) : Nat.card (Subgroup.center G) = p
  quotient_elementary_abelian (p) (G): IsElementaryAbelian p (G ⧸ (Subgroup.center G))
  quotient_nontrivial (p) (G) : Nontrivial (G ⧸ (Subgroup.center G))


public theorem CFSG.IsExtraspecial.center_isPGroup (p : ℕ) (G : Type*) [Group G] [IsExtraspecial p G] :
    IsPGroup p (Subgroup.center G) := by
    apply IsPGroup.of_card (n := 1)
    rw[pow_one]
    exact IsExtraspecial.center_order_p p G

public theorem CFSG.IsExtraspecial.quotient_isPGroup (p : ℕ) (G : Type*) [Group G] [IsExtraspecial p G] :
    IsPGroup p (G ⧸ (Subgroup.center G)) :=
  haveI := IsExtraspecial.quotient_elementary_abelian p G
  IsElementaryAbelian.isPGroup p (G ⧸ (Subgroup.center G))

theorem IsPGroup.of_normal_qotient {p : ℕ} {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]
    (hN : IsPGroup p N) (hQ : IsPGroup p (G ⧸ N)) : IsPGroup p G := fun g => by
  rcases hQ (g : G ⧸ N) with ⟨k₁, hk₁⟩
  rw [← @QuotientGroup.mk_pow G _ N _ g (p ^ k₁), QuotientGroup.eq_one_iff] at hk₁
  rcases hN ⟨g ^ (p ^ k₁), hk₁⟩ with ⟨k₂, hk₂⟩
  use k₁ + k₂
  rw [SubmonoidClass.mk_pow, Subgroup.mk_eq_one, ← pow_mul, ← pow_add] at hk₂
  exact hk₂

public theorem CFSG.IsExtraspecial.isPGroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [IsExtraspecial p G] : IsPGroup p G := by
  let _ := (inferInstance : Fact p.Prime)
  exact IsPGroup.of_normal_qotient (Subgroup.center G) (IsExtraspecial.center_isPGroup p G)
    (IsExtraspecial.quotient_isPGroup p G)
