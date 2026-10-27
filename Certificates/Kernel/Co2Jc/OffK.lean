module

public import Certificates.Kernel.Co2Jc.OffTw
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Native

theorem tabs_k : (tabs == tabsL) = true := by decide +kernel

theorem keys_k : decide ((tabsL.map enc).Nodup) = true := by decide +kernel

theorem mul_k : ∀ s < 256, mulRowK s = true := by kc_cover 16

theorem fix_k : ∀ i < 256, fixRowK i = true := by kc_cover 16

theorem par_k : ((List.range 256).all fun i => i == 0 ||
    (decide (parL i < i) && decide (parG i < 4) && Nat.beq (mulL (gI (parG i)) (parL i)) i)) =
      true := by
  decide +kernel

theorem gens_k : (gens.length == 4 && (List.range 4).all fun k => decide (gI k < 256) &&
    gens.getD k [] == tabsL.getD (gI k) []) = true := by
  decide +kernel

theorem tab_k : (tabsL.getD 0 [] == idTab &&
    tabsL.all fun l => decide (l.length = 10) && l.all (fun c => decide (c < 1024))) = true := by
  decide +kernel

theorem subs_k : ((subs.length == 715) &&
    subs.all fun l => l.contains 0 && l.all (fun i => decide (i < 256)) && decide (l.Nodup)) =
      true := by
  decide +kernel

theorem invol_k : ((List.range 256).all fun s =>
    (s == 0) || !(Nat.beq (mulL s s) 0) || subs.contains (pairOf s)) = true := by
  decide +kernel

theorem off_neg : (!Nat.beq (PT 1) (CFSG.KC.M1F2.mulF 10 (PT 0) (PT 0)) &&
    !decide ((subs.getD 0 []).length *
      ((List.range 1024).filter fun m => (andM (subs.getD 0 [])).testBit m).length ≤ 1)) =
      true := by
  decide +kernel

end CertificateChecks.KernelCo2Jc
