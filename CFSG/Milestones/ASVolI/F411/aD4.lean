module

public import CFSG.Milestones.ASVolI.F411.Cent
public import CFSG.Milestones.ASVolI.F411.aD4Core

public section

namespace CFSG.ASVolI

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial

section D4


theorem burnsideF411a_autCentSylow_D4 (p d : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hd : 1 ≤ d) (hK : Nat.card K = (p ^ d) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ d)) :
    burnsideF411_AutCentSylow
      ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K
        σ.toRingHom) p := by
  have hK' : Nat.card K = p ^ (d * 3) := by rw [hK, ← pow_mul]
  have : CharP K p := finite_field_prime_power_characteristic (Fact.out : p.Prime) (by omega) hK'
  exact fun α S hα => burnsideF411a_D4_inner_of_fix_sylow hd hK σ hσ α S hα

end D4

end CFSG.ASVolI
