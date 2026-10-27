module

public import CFSG.Quasithin.EmptyFaithfulMultiple.CatalogNative
public import CFSG.Quasithin.Background.G2UGroups

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Assembly.LowTwoRank

theorem g2TwoDerivedUnitaryTransport_holds
    : G2TwoDerivedUnitaryTransport := by
  intro k _ _ hk
  have := Fintype.ofFinite k
  have hc : Fintype.card k = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hk, ZMod.card]
  let e := (G2U.commutatorAdjointEquiv (FiniteField.ringEquivOfCardEq hc)).trans
    G2U.commutatorRootGroupEquiv
  obtain ⟨hadm, K, _, _, hK, ⟨e'⟩⟩ :=
    LinearGroups.UnitaryThreeOverNine.classicalModel_statedSU G2U.card_F9
  exact Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

end CFSG.Quasithin.EmptyFaithfulMultiple
