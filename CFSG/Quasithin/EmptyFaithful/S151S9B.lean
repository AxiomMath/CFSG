module

public import CFSG.Quasithin.EmptyFaithful.A38cOrders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders
  CFSG.Quasithin.H13.VolI CFSG.Quasithin.Vol2.Ch10.SecA CFSG.LieType.BorelTits
open scoped Pointwise

theorem not_a38Order_44352000 : ¬ A38Order 44352000 :=
  not_a38Order_of (a := 9) (b := 86625) (by norm_num) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 9) hp hp3 ⟨86625, by norm_num⟩ (by norm_num))

theorem not_a38Order_145926144000 : ¬ A38Order 145926144000 :=
  not_a38Order_of (a := 14) (b := 8906625) (by norm_num) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (fun p hp hp3 => ordA_one_ne_of_two_pow (N := 14) hp hp3 ⟨8906625, by norm_num⟩
      (by norm_num))

theorem hsru_not_a38Types
    {X : Type} [Group X] (h : IsSporadic .HS X ∨ IsSporadic .Ru X) : ¬ A38Types X := by
  intro hA
  have hc := a38Order_card hA
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv,
      show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .HS) = 44352000 from
        CFSG.Sporadic.HS.card_HS] at hc
    exact not_a38Order_44352000 hc
  · rw [Nat.card_congr e.toEquiv,
      show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ru) = 145926144000 from
        CFSG.Sporadic.Ru.card_Ru] at hc
    exact not_a38Order_145926144000 hc

end CFSG.Quasithin
