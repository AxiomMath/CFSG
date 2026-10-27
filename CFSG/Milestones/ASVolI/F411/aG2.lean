module

public import CFSG.Milestones.ASVolI.F411.Cent
public import CFSG.Milestones.ASVolI.F411.aG2Core

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section G2


theorem burnsideF411a_autCentSylow_chevalley (τ : Tag) (K : Type) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] : burnsideF411_AutCentSylow (adjointGroup τ K) p :=
  fun α S hα => burnsideF411a_chev_inner_of_fix_sylow τ K p α S hα

theorem burnsideF411a_autCentSylow_G2 (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hK : 3 ≤ Nat.card K) :
    burnsideF411_AutCentSylow
      (CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 K) p :=
  burnsideF411a_autCentSylow_chevalley Tag.G2 K p

end G2

end CFSG.ASVolI
