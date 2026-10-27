module

public import CFSG.Permutation.FiveTransitive.OyamaNoCondition
public import CFSG.Permutation.FiveTransitive.OyamaCyclicDescent

public section

namespace CFSG

namespace FiveTransitive.OyamaFixedSixExclusion

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem not_even_fixed_six
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (a : Fin 4 ↪ X)
    (P : Sylow 2 (stabilizer G a)) (hP : (P : Subgroup (stabilizer G a)) ≠ ⊥)
    (hfix : Nat.card (fixedPoints (ambientSylow a P) X) = 6)
    (heven : EvenSixTupleLocal.EvenFixed G X (ambientSylow a P)) : False := by
  obtain ⟨Q, _, _, hcond, _, _⟩ :=
    OyamaCyclicDescent.exists_descended_action h4 a P hP hfix heven
  let _ := Fintype.ofFinite (Fixed (X := X) Q)
  exact OyamaNoCondition.not_condition hcond

end FiveTransitive.OyamaFixedSixExclusion

end CFSG
