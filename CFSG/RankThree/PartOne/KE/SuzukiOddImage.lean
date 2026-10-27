module

public import CFSG.RankThree.PartOne.KE.SuzukiPlane
public import CFSG.RankThree.PartOne.KE.Basic

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne

theorem suzukiNormalizedComponentLocalCoreProductOddImage_of_plane
    (hplane : ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p →
        PlaneLocalCoreOdd p (suzukiGroup a K)) :
    SuzukiNormalizedComponentLocalCoreProductOddImage := by
  intro H _ _ p hp hp3 E hE hEc t ht ht1 L hL ℓ f hmod hEL hSL
  obtain ⟨hℓ, a, ha, K, _, _, hf, hKcard, ⟨e⟩⟩ := hmod
  have hKcard' : Nat.card K = 2 ^ (2 * a + 1) := hf ▸ hKcard
  have hplane' : PlaneLocalCoreOdd p (L ⧸ Subgroup.center L) :=
    PlaneLocalCoreOdd.of_mulEquiv hp e (hplane a ha K hKcard' p hp hp3)
  obtain ⟨hset, hWN, hodd, hres, hnonf⟩ := component_local_core_odd_action_of_plane hp
    (by omega) hE hEc ht ht1 hL hEL hSL hplane'
  exact ⟨componentLocalCoreOddImage_of_residual hL ⟨⟨hset, hWN, hodd⟩, hres⟩, hnonf⟩

theorem suzukiNormalizedComponentLocalCoreProductOddImage_of_descent
    (hdesc : SuzukiPrimeFieldCosetDescent) : SuzukiNormalizedComponentLocalCoreProductOddImage :=
  suzukiNormalizedComponentLocalCoreProductOddImage_of_plane fun _ ha _ _ _ hK _ hp hp3 =>
    suzuki_planeLocalCoreOdd_of_descent hdesc ha hK hp hp3

end CFSG.RankThree.PartOne.KE
