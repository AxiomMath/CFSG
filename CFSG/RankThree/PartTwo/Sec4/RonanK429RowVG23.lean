module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace RowV


theorem card_g2_three_dvd :
    Nat.card (TauCeti.CFSGIndex.lie g2ThreeIndex).Group ∣ CFSG.Open.ordG2 3 := by
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ :=
    Census.chevalleyExceptionalModel_G2_three q g2ThreeIndex.2 rfl rfl
  have h2 : Nat.card (TauCeti.CFSGIndex.lie g2ThreeIndex).Group =
      Nat.card (Blueprint.AdjointQuotient .G2 K) := Nat.card_congr φ.toEquiv
  rw [h2]
  have h := Subgroup.card_quotient_dvd_card (Subgroup.center ↥(adjointGroup .G2 K))
  rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK, pow_one] at h
  exact h

theorem noCfgS429_g2_three {S : Type} [Group S] [Finite S]
    (φ : S ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) : NoCfgS429 S :=
  noCfgS429_of_card (N := CFSG.Open.ordG2 3) (B := 9)
    (by rw [Nat.card_congr φ.toEquiv]; exact card_g2_three_dvd)
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
