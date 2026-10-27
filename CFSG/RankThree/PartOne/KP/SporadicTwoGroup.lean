module

public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne

theorem not_dvd_card_of_isPGroup_two {G : Type*} [Group G] (hfin : Finite G) (h2 : IsPGroup 2 G)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) : ¬ q ∣ Nat.card G := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
  rw [hk] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd)
  omega

end CFSG.RankThree.PartOne
