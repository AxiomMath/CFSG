module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTwOmPlus_facts_rec
    {K : Type} [Field K] [Finite K] [CharP K 2] {m r : ℕ}
    (hr : 3 ≤ r) (hmr : m = r + 1) :
    Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) = ⊥ ∧
      GGOutdiagPrime 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
        (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))) ∧
      GGCenterPrime 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) := by
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) (p := 3) Nat.prime_three
    (by norm_num) (by omega : 3 ≤ m)
  exact ⟨hZ, fun φ hφ _ => hφ, hcp⟩

end CFSG.StandardType

end
