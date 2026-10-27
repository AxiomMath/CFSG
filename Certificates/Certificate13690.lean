module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Group
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

open CFSG.KD.Fi24ThreeO.Group

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three in
theorem certificate13690_of_bridge
    (hB : Bridge)
    (hlv : CFSG.Perm.Native.levelLetters CFSG.Sporadic.Fi24.letters
      CFSG.Sporadic.Fi24.Native.chainBase 3 = #[12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) :
 FixFacts [18] 221549 ∧ FixFacts [16, 19] 221549 ∧ FixFacts [14, 16, 16, 14, 16, 16] 14069 ∧
      Nat.card (MulAction.orbit (CFSG.Sporadic.Fi24.lvl 3) (⟨14069, by norm_num⟩ : Fin 306936)) =
        1152 ∧
      FixFacts [16] 221549 ∧ FreeFacts [2] ⟨12, by norm_num⟩ :=
  by
    intros
    exact ⟨fixFacts_of hB (r := 0) (by norm_num), fixFacts_of hB (r := 1) (by norm_num),
      fixFacts_of hB (r := 2) (by norm_num), orbit_lvl3 hB hlv, fixFacts_of hB (r := 3) (by norm_num),
      freeFacts_of hB⟩

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three in
theorem certificate13690 : 
    FixFacts [18] 221549 ∧ FixFacts [16, 19] 221549 ∧ FixFacts [14, 16, 16, 14, 16, 16] 14069 ∧
      Nat.card (MulAction.orbit (CFSG.Sporadic.Fi24.lvl 3) (⟨14069, by norm_num⟩ : Fin 306936)) =
        1152 ∧
      FixFacts [16] 221549 ∧ FreeFacts [2] ⟨12, by norm_num⟩ :=
  certificate13690_of_bridge KernelFi24OrbL.bridge (by
    intros
    rw [KernelFi24OrbL.levelLetters_eq 3 (by norm_num)]
    decide)

end Certificates
