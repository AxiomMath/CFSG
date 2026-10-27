module

public import CFSG.Monster.B.E6.StandardSimple

public section

namespace CFSG.Monster.Existence

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std

theorem nonempty_mulEquiv_derivedCentralQuotient {M : Type} [Group M] {H N : Subgroup M}
    (hN : ⁅H, H⁆ = N) (hZ : Subgroup.center ↥N = ⊥) :
    Nonempty (↥N ≃* DerivedCentralQuotient H) := by
  subst hN
  exact ⟨(QuotientGroup.quotientBot (G := ↥⁅H, H⁆)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)⟩

theorem lieModel_twistedE6_of_mulEquiv {G : Type} [Group G] (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ TwistTag.E6.order) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    (e : Nonempty (G ≃* DerivedCentralQuotient (twistedFixedGroup TwistTag.E6 K σ))) :
    LieModel G .twistedE6 0 2 1 :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl⟩, K, inferInstance, inferInstance,
    hK, σ, hσ, e⟩)

theorem commutator_stdFixedGroup :
    ⁅stdFixedGroup, stdFixedGroup⁆ = stdGroup :=
  (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two le_rfl K
    CFSG.Monster.B.E6.card_K barHom CFSG.Monster.B.E6.barHom_eq_pow).2.2.1

theorem center_stdGroup_eq_bot :
    Subgroup.center ↥stdGroup = ⊥ :=
  center_graphFixedRootGroup_eq_bot (t := TwistTag.E6) CFSG.Monster.B.E6.barHom_bijective.2

theorem lieModel_stdGroup :
    LieModel ↥stdGroup .twistedE6 0 2 1 :=
  lieModel_twistedE6_of_mulEquiv K CFSG.Monster.B.E6.card_K barHom
    CFSG.Monster.B.E6.barHom_eq_pow
    (nonempty_mulEquiv_derivedCentralQuotient commutator_stdFixedGroup center_stdGroup_eq_bot)

end CFSG.Monster.Existence
