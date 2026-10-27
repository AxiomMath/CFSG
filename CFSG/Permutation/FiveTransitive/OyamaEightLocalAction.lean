module

public import CFSG.Permutation.FiveTransitive.OyamaNormalizerTwoTransitive
public import CFSG.Permutation.FiveTransitive.TwoTransitiveA6Card

public section

namespace CFSG

namespace FiveTransitive.OyamaEightLocalAction

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem normalizer_card
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (b:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G b)) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    Nat.card (FixedSetNormalizerHom.fixedPermHom G X A).range=60 ∨
      Nat.card (FixedSetNormalizerHom.fixedPermHom G X A).range=360 := by
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let _ := Fintype.ofFinite (fixedPoints A X)
  let _ : DecidableEq (fixedPoints A X) := Classical.decEq _
  have hc:Fintype.card (fixedPoints A X)=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact (hcond.2.1 b P).1
  exact TwoTransitiveA6Card.card_eq_sixty_or_three_hundred_sixty hc _
    (OyamaNormalizerTwoTransitive.image_le_alternating hcond b P)
    (OyamaNormalizerTwoTransitive.two_transitive hcond b P)

end FiveTransitive.OyamaEightLocalAction

end CFSG
