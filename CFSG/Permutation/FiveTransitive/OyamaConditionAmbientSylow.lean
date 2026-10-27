module

public import CFSG.Permutation.FiveTransitive.FourTransitiveTwoPart
public import CFSG.Permutation.FiveTransitive.OyamaConditionDegreeEight

public section

namespace CFSG

namespace FiveTransitive.OyamaConditionAmbientSylow

open MulAction

private theorem card_eq_sixteen_of_degree_mod_eight
    {G X:Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (hdegree:Nat.card X%8=6)
    (T:Sylow 2 G) : Nat.card T=16 := by
  classical
  let b:Fin 4 ↪ X := (Fin.castLEEmb (by have := hcond.1; omega : 4≤Nat.card X)).trans
    (Finite.equivFin X).symm.toEmbedding
  let P:Sylow 2 (stabilizer G b) := Classical.arbitrary _
  exact FourTransitiveTwoPart.ambient_sylow_card_sixteen
    (OyamaConditionFourTransitive.four_transitive hcond) hdegree b P
    (OyamaConditionSylowTwo.card_eq_two hcond b P) T

theorem card_eq_sixteen
    {G X:Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (T:Sylow 2 G) : Nat.card T=16 :=
  card_eq_sixteen_of_degree_mod_eight hcond (OyamaConditionDegreeEight.degree_mod_eight hcond) T

end FiveTransitive.OyamaConditionAmbientSylow

end CFSG
