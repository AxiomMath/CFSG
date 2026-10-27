module

public import CFSG.Quasithin.EmptyFaithful.S1421QShapeDefs
public import CFSG.Quasithin.EmptyFaithful.S1421QNSNum

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421NS

theorem dvd_card_of_isCentralL3Sp4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsCentralL3Sp4 n X) :
    (n = 2 → 7 ∣ Nat.card X ∨ 17 ∣ Nat.card X) ∧
    (n = 3 → 73 ∣ Nat.card X ∨ 13 ∣ Nat.card X) := by
  have hdvd : Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card X := Subgroup.card_quotient_dvd_card _
  rcases h with h | h
  · have := dvd_card_of_isPSL_three h
    exact ⟨fun hn => Or.inl ((this.1 hn).trans hdvd), fun hn => Or.inl ((this.2 hn).trans hdvd)⟩
  · have := dvd_card_of_isPSp_four h
    exact ⟨fun hn => Or.inr ((this.1 hn).trans hdvd), fun hn => Or.inr ((this.2 hn).trans hdvd)⟩

end S1421NS

end CFSG.Quasithin
