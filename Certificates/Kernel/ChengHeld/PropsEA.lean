module

public import Certificates.Kernel.ChengHeld.PropsAut
public import Certificates.Data.Kernel.ChengHeldEAK
meta import Certificates.Data.ChengHeldSec2Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.P

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel

meta def eaInvsM (α : Nat) : Array Nat :=
  let M := mkReg α
  ((List.range M.N).filter fun a => a != 0 && M.m a a == 0).toArray

meta def eaImgM (M : RegModel) (a E : Nat) : Nat :=
  (List.range M.N).foldl (fun acc x => if E.testBit x then acc ||| (1 <<< M.m a x) else acc) 0

meta def eaCentM (M : RegModel) (a : Nat) : Nat :=
  (List.range M.N).foldl (fun acc x => if M.m a x == M.m x a then acc ||| (1 <<< x) else acc) 0

meta def eaLevM (α : Nat) : Array (Array Nat) := Id.run do
  let M := mkReg α
  let invs := eaInvsM α
  let mut L : Array (Array Nat) := invs.map fun a => #[0, a]
  let mut out : Array (Array Nat) := #[]
  for _ in [0:6] do
    out := out.push ((L.map eaMask).qsort (· < ·))
    L := M.eaNext invs L
  return out

meta def eaAM (α : Nat) : Array (Array Nat) :=
  let M := mkReg α
  let invs := eaInvsM α
  #[invs, (Array.range M.N).map fun x => ((List.range invs.size).find? fun t => invs[t]! == x).getD 0]

meta def eaCM (α : Nat) : Array (Array Nat) :=
  let M := mkReg α
  #[(eaInvsM α).map fun a => eaCentM M a]

meta def eaIdxM (A : Array Nat) (F : Nat) : Nat :=
  ((List.range A.size).find? fun i => A[i]! == F).getD 0

meta def eaExtM (M : RegModel) (invs CM : Array Nat) (Lk : Array Nat) : Array (Nat × Nat × Nat) :=
  Id.run do
    let mut out : Array (Nat × Nat × Nat) := #[]
    for j in [0:Lk.size] do
      let E := Lk[j]!
      for t in [0:invs.size] do
        let a := invs[t]!
        if !E.testBit a && (E &&& CM[t]!) == E then
          out := out.push (j, t, E ||| eaImgM M a E)
    return out

meta def eaPM (α : Nat) : Array (Array Nat) := Id.run do
  let M := mkReg α
  let invs := eaInvsM α
  let CM := (eaCM α)[0]!
  let Lv := eaLevM α
  let mut out : Array (Array Nat) := #[]
  for k in [1:6] do
    let ext := eaExtM M invs CM Lv[k - 1]!
    let next := Lv[k]!
    let mut pj : Array Nat := Array.replicate next.size 0
    let mut pt : Array Nat := Array.replicate next.size 0
    let mut done : Array Bool := Array.replicate next.size false
    for e in ext do
      let i := eaIdxM next e.2.2
      if !done[i]! then
        done := done.set! i true
        pj := pj.set! i e.1
        pt := pt.set! i e.2.1
    out := (out.push pj).push pt
  return out

meta def eaWM (α : Nat) : Array (Array Nat) := Id.run do
  let M := mkReg α
  let invs := eaInvsM α
  let CM := (eaCM α)[0]!
  let Lv := eaLevM α
  let mut out : Array (Array Nat) := #[]
  for k in [0:5] do
    let Lk := Lv[k]!
    for j in [0:Lk.size] do
      let E := Lk[j]!
      out := out.push ((Array.range invs.size).map fun t =>
        let a := invs[t]!
        if !E.testBit a && (E &&& CM[t]!) == E then eaIdxM Lv[k + 1]! (E ||| eaImgM M a E)
        else 0)
  return out

meta def eaA0 : Array (Array Nat) := eaAM 0
meta def eaA1 : Array (Array Nat) := eaAM 1
meta def eaA2 : Array (Array Nat) := eaAM 2
meta def eaC0 : Array (Array Nat) := eaCM 0
meta def eaC1 : Array (Array Nat) := eaCM 1
meta def eaC2 : Array (Array Nat) := eaCM 2
meta def eaL0 : Array (Array Nat) := eaLevM 0
meta def eaL1 : Array (Array Nat) := eaLevM 1
meta def eaL2 : Array (Array Nat) := eaLevM 2
meta def eaP0 : Array (Array Nat) := eaPM 0
meta def eaP1 : Array (Array Nat) := eaPM 1
meta def eaP2 : Array (Array Nat) := eaPM 2
meta def eaW0 : Array (Array Nat) := eaWM 0
meta def eaW1 : Array (Array Nat) := eaWM 1
meta def eaW2 : Array (Array Nat) := eaWM 2

end CertificateChecks.KernelChengHeld.P

#kc_items CertificateChecks.KernelChengHeld.P.EAA0 include_bytes "data/PropsEA.EAA0.items" 343 9911130801623358124
#kc_items CertificateChecks.KernelChengHeld.P.EAA1 include_bytes "data/PropsEA.EAA1.items" 343 9911130801623358124
#kc_items CertificateChecks.KernelChengHeld.P.EAA2 include_bytes "data/PropsEA.EAA2.items" 185 12346240088748495663
#kc_items CertificateChecks.KernelChengHeld.P.EAC0 include_bytes "data/PropsEA.EAC0.items" 1763 12119534640461938334
#kc_items CertificateChecks.KernelChengHeld.P.EAC1 include_bytes "data/PropsEA.EAC1.items" 1763 12119534640461938334
#kc_items CertificateChecks.KernelChengHeld.P.EAC2 include_bytes "data/PropsEA.EAC2.items" 884 12200550803213062984
#kc_items CertificateChecks.KernelChengHeld.P.EAL0 include_bytes "data/PropsEA.EAL0.items" 7285 3947503702488698709
#kc_items CertificateChecks.KernelChengHeld.P.EAL1 include_bytes "data/PropsEA.EAL1.items" 7285 10387830311964189410
#kc_items CertificateChecks.KernelChengHeld.P.EAL2 include_bytes "data/PropsEA.EAL2.items" 11720 11371544314303987229
#kc_items CertificateChecks.KernelChengHeld.P.EAP0 include_bytes "data/PropsEA.EAP0.items" 468 3451696338080736168
#kc_items CertificateChecks.KernelChengHeld.P.EAP1 include_bytes "data/PropsEA.EAP1.items" 468 9213859516287802194
#kc_items CertificateChecks.KernelChengHeld.P.EAP2 include_bytes "data/PropsEA.EAP2.items" 1727 11413434794813738698
#kc_items CertificateChecks.KernelChengHeld.P.EAW0 include_bytes "data/PropsEA.EAW0.items" 10311 5980965431902527029
#kc_items CertificateChecks.KernelChengHeld.P.EAW1 include_bytes "data/PropsEA.EAW1.items" 10311 17946240673316463470
#kc_items CertificateChecks.KernelChengHeld.P.EAW2 include_bytes "data/PropsEA.EAW2.items" 41039 8540385958716741854

namespace CertificateChecks.KernelChengHeld.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ChengHeldS2 CFSG.KC.ChengHeldP
open CFSG.OddStandard.ChengHeldData CertificateChecks.KernelChengHeld
open CertificateChecks.KernelChengHeld.S2 (IX0 IX1 IV0 IV1)

theorem p6138_ea0i : bAnd(eaInvW 256 9 CH0.T (IX0 0) (EAA0 0) (EAA0 1) 55,
    bAnd(eaCMW 256 9 CH0.T (IX0 0) (IV0 0) (EAA0 0) (EAC0 0) 55,
      eaL1W 256 9 (EAA0 0) (EAL0 0) 55)) = true := by
  quickRfl

theorem p6138_ea0u : bAnd(eaUpW 256 9 CH0.T (IX0 0) (EAA0 0) (EAC0 0) 55 (EAL0 0) 55 (EAL0 1) 143
      (EAP0 0) (EAP0 1),
    eaUpW 256 9 CH0.T (IX0 0) (EAA0 0) (EAC0 0) 55 (EAL0 1) 143 (EAL0 2) 29 (EAP0 2) (EAP0 3)) =
    true := by
  quickRfl

theorem p6138_ea0w : bAnd(eaWitW 256 9 (EAA0 0) (EAC0 0) 55 (EAL0 0) 55 (EAL0 1) 143 EAW0 0,
    bAnd(eaWitW 256 9 (EAA0 0) (EAC0 0) 55 (EAL0 1) 143 (EAL0 2) 29 EAW0 55,
      eaWitW 256 9 (EAA0 0) (EAC0 0) 55 (EAL0 2) 29 (EAL0 3) 0 EAW0 198)) = true := by
  quickRfl

theorem p6138_ea1i : bAnd(eaInvW 256 9 CH1.T (IX1 0) (EAA1 0) (EAA1 1) 55,
    bAnd(eaCMW 256 9 CH1.T (IX1 0) (IV1 0) (EAA1 0) (EAC1 0) 55,
      eaL1W 256 9 (EAA1 0) (EAL1 0) 55)) = true := by
  quickRfl

theorem p6138_ea1u : bAnd(eaUpW 256 9 CH1.T (IX1 0) (EAA1 0) (EAC1 0) 55 (EAL1 0) 55 (EAL1 1) 143
      (EAP1 0) (EAP1 1),
    eaUpW 256 9 CH1.T (IX1 0) (EAA1 0) (EAC1 0) 55 (EAL1 1) 143 (EAL1 2) 29 (EAP1 2) (EAP1 3)) =
    true := by
  quickRfl

theorem p6138_ea1w : bAnd(eaWitW 256 9 (EAA1 0) (EAC1 0) 55 (EAL1 0) 55 (EAL1 1) 143 EAW1 0,
    bAnd(eaWitW 256 9 (EAA1 0) (EAC1 0) 55 (EAL1 1) 143 (EAL1 2) 29 EAW1 55,
      eaWitW 256 9 (EAA1 0) (EAC1 0) 55 (EAL1 2) 29 (EAL1 3) 0 EAW1 198)) = true := by
  quickRfl

theorem p6138_ea2i : bAnd(eaInvW 128 8 CH2.T (IX2 0) (EAA2 0) (EAA2 1) 55,
    bAnd(eaCMW 128 8 CH2.T (IX2 0) (IV2 0) (EAA2 0) (EAC2 0) 55,
      eaL1W 128 8 (EAA2 0) (EAL2 0) 55)) = true := by
  quickRfl

theorem p6138_ea2u : bAnd(eaUpW 128 8 CH2.T (IX2 0) (EAA2 0) (EAC2 0) 55 (EAL2 0) 55 (EAL2 1) 303
      (EAP2 0) (EAP2 1),
    bAnd(eaUpW 128 8 CH2.T (IX2 0) (EAA2 0) (EAC2 0) 55 (EAL2 1) 303 (EAL2 2) 309 (EAP2 2) (EAP2 3),
    bAnd(eaUpW 128 8 CH2.T (IX2 0) (EAA2 0) (EAC2 0) 55 (EAL2 2) 309 (EAL2 3) 62 (EAP2 4) (EAP2 5),
      eaUpW 128 8 CH2.T (IX2 0) (EAA2 0) (EAC2 0) 55 (EAL2 3) 62 (EAL2 4) 2 (EAP2 6) (EAP2 7)))) =
    true := by
  quickRfl

theorem p6138_ea2w : bAnd(eaWitW 128 8 (EAA2 0) (EAC2 0) 55 (EAL2 0) 55 (EAL2 1) 303 EAW2 0,
    bAnd(eaWitW 128 8 (EAA2 0) (EAC2 0) 55 (EAL2 1) 303 (EAL2 2) 309 EAW2 55,
    bAnd(eaWitW 128 8 (EAA2 0) (EAC2 0) 55 (EAL2 2) 309 (EAL2 3) 62 EAW2 358,
    bAnd(eaWitW 128 8 (EAA2 0) (EAC2 0) 55 (EAL2 3) 62 (EAL2 4) 2 EAW2 667,
      eaWitW 128 8 (EAA2 0) (EAC2 0) 55 (EAL2 4) 2 (EAL2 5) 0 EAW2 729)))) = true := by
  quickRfl

theorem p6138_eaz : bAnd(bAnd(eaUpW 256 9 CH0.T (IX0 0) (EAA0 0) (EAC0 0) 55 (EAL0 2) 29 (EAL0 3) 0
      (EAP0 4) (EAP0 5),
    bAnd(eaUpW 256 9 CH0.T (IX0 0) (EAA0 0) (EAC0 0) 55 (EAL0 3) 0 (EAL0 4) 0 (EAP0 6) (EAP0 7),
    bAnd(eaUpW 256 9 CH0.T (IX0 0) (EAA0 0) (EAC0 0) 55 (EAL0 4) 0 (EAL0 5) 0 (EAP0 8) (EAP0 9),
    bAnd(eaWitW 256 9 (EAA0 0) (EAC0 0) 55 (EAL0 3) 0 (EAL0 4) 0 EAW0 227,
      eaWitW 256 9 (EAA0 0) (EAC0 0) 55 (EAL0 4) 0 (EAL0 5) 0 EAW0 227)))),
    bAnd(bAnd(eaUpW 256 9 CH1.T (IX1 0) (EAA1 0) (EAC1 0) 55 (EAL1 2) 29 (EAL1 3) 0
      (EAP1 4) (EAP1 5),
    bAnd(eaUpW 256 9 CH1.T (IX1 0) (EAA1 0) (EAC1 0) 55 (EAL1 3) 0 (EAL1 4) 0 (EAP1 6) (EAP1 7),
    bAnd(eaUpW 256 9 CH1.T (IX1 0) (EAA1 0) (EAC1 0) 55 (EAL1 4) 0 (EAL1 5) 0 (EAP1 8) (EAP1 9),
    bAnd(eaWitW 256 9 (EAA1 0) (EAC1 0) 55 (EAL1 3) 0 (EAL1 4) 0 EAW1 227,
      eaWitW 256 9 (EAA1 0) (EAC1 0) 55 (EAL1 4) 0 (EAL1 5) 0 EAW1 227)))),
    eaUpW 128 8 CH2.T (IX2 0) (EAA2 0) (EAC2 0) 55 (EAL2 4) 2 (EAL2 5) 0 (EAP2 8) (EAP2 9))) =
    true := by
  quickRfl

theorem p6138_neg_eaI : (!eaInvW 256 9 CH0.T (IX0 0) (EAA0 1) (EAA0 1) 55) = true := by quickRfl

theorem p6138_neg_eaC :
    (!eaCMW 256 9 CH0.T (IX0 0) (IV0 0) (EAA0 0) (EAL0 1) 55) = true := by quickRfl

theorem p6138_neg_eaL : (!eaL1W 128 8 (EAA2 0) (EAL2 1) 55) = true := by quickRfl

theorem p6138_neg_eaU : (!eaUpW 128 8 CH2.T (IX2 0) (EAA2 0) (EAC2 0) 55 (EAL2 1) 303 (EAL2 2) 309
    (EAP2 3) (EAP2 2)) = true := by quickRfl

theorem p6138_neg_eaW :
    (!eaWitW 128 8 (EAA2 0) (EAC2 0) 55 (EAL2 1) 303 (EAL2 2) 308 EAW2 55) = true := by quickRfl

end CertificateChecks.KernelChengHeld.P

end
