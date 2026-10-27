module

public import CFSG.GroupTheory.PRankBound
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open

theorem twentySeven_dvd_of_three_le_pRank {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (h : 3 ≤ CFSG.Open.pRank 3 H) : 27 ∣ Nat.card H := by
  by_contra hn
  have := CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := H) (p := 3) (k := 2)
    Nat.prime_three (by simpa using hn)
  omega

end CFSG.StandardType.FF81.CatQ1
