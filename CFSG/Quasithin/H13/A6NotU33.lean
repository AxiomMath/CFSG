module

public import CFSG.Quasithin.H13.A6Setting4
import CFSG.Adapters.LieModelSmallOrders

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem card_of_lieModel_psu33 {X : Type} [Group X] (h : LieModel X .PSU 3 3 1) :
    Nat.card X = 6048 :=
  CFSG.Blueprint.LieModel.card_psu_three_three h

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem not_lieModel_psu33 : ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := by
  intro h
  have h1 := card_of_lieModel_psu33 h
  obtain ⟨e⟩ := S.centralQuot
  have h2 : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 360 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  rw [h1, h2] at h3
  omega

end Setting4

end CFSG.Quasithin.H13.A6
