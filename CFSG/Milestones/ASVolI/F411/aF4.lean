module

public import CFSG.Milestones.ASVolI.F411.Cent
public import CFSG.Milestones.ASVolI.F411.aF4Core

public section

namespace CFSG.ASVolI

open CFSG.LieType.Ree

section F4


theorem burnsideF411a_autCentSylow_F4 (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    burnsideF411_AutCentSylow ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) 2 :=
  fun α S hα => burnsideF411a_F4_inner_of_fix_sylow a ha K hK α S hα

end F4

end CFSG.ASVolI
