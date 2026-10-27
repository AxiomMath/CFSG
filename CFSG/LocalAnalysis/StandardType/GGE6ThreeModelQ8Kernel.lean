module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag

import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
import CFSG.LieType.Steinberg.CentralExt.TwistedE6PosLift
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKernelCore

public section

namespace CFSG.StandardType

namespace TwE6Delta

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Minuscule


theorem card_ker_dvd_three_q8 {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 3 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Nat.card ψ.ker ∣ 3 := by
  obtain ⟨q, hq, hqk⟩ := exists_sc_surjection (by omega : 1 ≤ n) hK
  have : Finite (twistedE6Group 2 n) := by
    have : Finite (Module.End (GaloisField 2 (2 * n)) (Fin e6Data.d →₀ GaloisField 2 (2 * n))) :=
      Module.finite_of_finite (GaloisField 2 (2 * n))
    infer_instance
  have h5 : 5 ≤ 2 ^ n :=
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hk : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := card_galoisField_two_mul 2 n (by omega)
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* twistedE6Group 2 n),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : twistedE6Group 2 n →* E, ∀ h, π (s h) = h :=
    fun E _ _ π hπ hc => TwistedE6Closed.twistedE6_exists_section_of_central
      (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n) (q := 2 ^ n) h5 hk
      (fun c => by rw [frobQ_apply]) hπ hc
  have h1 := E6ThreeKernel.card_ker_dvd_of_split hq hsplit hψ hker hperf
  have hcard : Nat.card (Subgroup.center (twistedE6Group 2 n)) = Nat.gcd 3 (2 ^ n + 1) :=
    (TwistedE6Closed.card_center_fixedGroup (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n)
      (q := 2 ^ n) hk (fun c => by rw [frobQ_apply])).1
  have h3 : Nat.card (Subgroup.center (twistedE6Group 2 n)) ∣ 3 := by
    rw [hcard]
    exact Nat.gcd_dvd_left 3 _
  exact h1.trans ((Subgroup.card_dvd_of_le hqk).trans h3)

end TwE6Delta

end CFSG.StandardType
