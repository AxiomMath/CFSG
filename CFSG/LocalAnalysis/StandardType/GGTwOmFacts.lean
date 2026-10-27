module

public import CFSG.LocalAnalysis.StandardType.GGTwAutDefs
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTwOm_facts_rec
    {K : Type} [Field K] [Finite K] [CharP K 2] {n m r : ℕ} {b c : K}
    (hK : Nat.card K = 2 ^ n) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hr : 3 ≤ r) (hmr : m = r)
    (h3 : 3 ∣ 2 ^ n - 1 ∨ (Odd r ∧ 3 ∣ 2 ^ n + 1)) :
    Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) = ⊥ ∧
      GGOutdiagPrime 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
        (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) ∧
      GGCenterPrime 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) := by
  subst hmr
  obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) (p := 3) Nat.prime_three
    (by norm_num) hr hbc
  exact ⟨hZ, fun φ hφ _ => hφ, hcp⟩

end CFSG.StandardType

end
