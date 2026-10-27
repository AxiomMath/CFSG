module

public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Open.MonsterDefs

public section

namespace CFSG.Sporadic

open Blueprint.NativeSporadic

theorem finite_carrier_of_ne_M (s : TauCeti.SporadicName) (hs : s ≠ .M) : Finite (Carrier s) := by
  cases s <;> first | exact absurd rfl hs | (dsimp [Carrier]; infer_instance)

theorem finite_carrier_M_of_card (h : Nat.card Open.MonsterY443Derived = Open.monsterOrder) :
    Finite (Carrier .M) := by
  have hpos : Nat.card Open.MonsterY443Derived ≠ 0 := by
    rw [h]; unfold Open.monsterOrder; norm_num
  have : Finite Open.MonsterY443Derived := Nat.finite_of_card_ne_zero hpos
  exact Finite.of_equiv _ Bridge.Y443.commutatorMulEquiv.toEquiv.symm

theorem finite_of_sporadicRep (hM : Finite (Carrier .M)) {G : Type} [Group G]
    (hrep : SporadicRep G) : Finite G := by
  obtain ⟨s, ⟨e⟩⟩ := hrep
  have : Finite (Carrier s) := by
    by_cases hs : s = .M
    · subst hs; exact hM
    · exact finite_carrier_of_ne_M s hs
  exact Finite.of_equiv _ e.toEquiv.symm

end CFSG.Sporadic
