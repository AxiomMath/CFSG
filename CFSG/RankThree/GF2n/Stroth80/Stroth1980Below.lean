module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def Stroth1980Below (N : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < N → ∀ (M Q Z : Subgroup G), StrothHyp M Q Z →
    ∀ B : Subgroup G, (∃ g : G, B = conjSubgroup g Z) → B ≤ Q → B ≠ Z →
      StrothConclusion M Q Z B

theorem Stroth1980Below.mono {N N' : ℕ} (h : N ≤ N') (hb : Stroth1980Below N') :
    Stroth1980Below N :=
  fun G _ _ hG => hb G (lt_of_lt_of_le hG h)

theorem Stroth1980Below.zero : Stroth1980Below 0 :=
  fun G _ _ hG => absurd hG (Nat.not_lt_zero _)

theorem stroth1980_of_below (h : ∀ N : ℕ, Stroth1980Below N) : Stroth1980Statement :=
  fun G _ _ M Q Z H B hB hBQ hBZ =>
    h (Nat.card G + 1) G (Nat.lt_succ_self _) M Q Z H B hB hBQ hBZ

end CFSG.RankThree.GF2n.Stroth80
