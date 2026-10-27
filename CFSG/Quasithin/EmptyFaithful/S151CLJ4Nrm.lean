module

public import CFSG.Quasithin.EmptyFaithful.S151S9UNorm
public import CFSG.Quasithin.EmptyFaithful.S151WA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders
open CFSG.Quasithin.H13.VolI

namespace J4Excl

theorem not_a38Order_j4 : ¬ A38Order 86775571046077562880 :=
  not_a38Order_of (a := 21) (b := 41377816699065) (by norm_num) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (ordA_one_ne_of_factors (m := 86775571046077562880) (P := 44) (by norm_num)
      (lt_of_prime_dvd_of_factors
        (l := List.replicate 22 2 ++ [3, 3, 3, 5, 7, 11, 11, 11, 23, 29, 31, 37, 43]) (by norm_num)
        (by norm_num) (by decide)))

theorem not_a38Types_of_isSporadic_j4
    {G : Type} [Group G] {L : Subgroup G}
    (h : IsSporadic .J4 (↥L ⧸ CFSG.pCore 2 ↥L)) : ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L) := by
  intro hA
  have hc := a38Order_card hA
  obtain ⟨e⟩ := h
  have hN : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 86775571046077562880 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  rw [hN] at hc
  exact not_a38Order_j4 hc

theorem g1_le_normalizer_of_isSporadic_j4
    (h38 : A38ForSQTK)
    {G : Type} [Group G] [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : IsComponentOf L (g1_1516 Z₁))
    (hJ4 : IsSporadic .J4 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
  have hLcomp : L ∈ cComp (g1_1516 Z₁) :=
    Id2519.mem_cComp_of_isComponentIn (DoubleA3.isComponentIn_iff_open.mpr hcomp)
  have hsqtk : IsSQTKIn (g1_1516 Z₁) := hc.h18.five.2.2.sqtk
  exact GoldMLB.normalizes_of_not_a38 h38 hsqtk hLcomp fun hA =>
    not_a38Types_of_isSporadic_j4 hJ4 ((S151S9U.a38Types_image_iff hLcomp).mp hA)

end J4Excl

end CFSG.Quasithin
