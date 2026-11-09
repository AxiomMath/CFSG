module

public import Certificates.Data.Kernel.Co2Smith.Pts
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Kernel.Co2Smith.WDefs
public import Certificates.Kernel.Co2Smith.FixData
public import Certificates.Kernel.SporSch.Co2M.Seeds
import CFSG.Certificates.Kernel.Common.AllChunks
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native CFSG.KC.Enum

@[expose] noncomputable def fxIdx (Y : Nat) : Option Nat :=
  (List.range (FXN 0)).find? fun j => eqK Y (FXM j)

@[expose] noncomputable def fxIs (Y k : Nat) : Bool :=
  match fxIdx Y with
  | some j => fixCntK (FXP j) == k
  | none => false

@[expose] noncomputable def fxBindK : Bool :=
  allN (FXN 0) fun j => bindVK (KernelSporSch.Co2M.PV 0) (FXP j) (CFSG.KC.Co1F2.trK 22 (FXM j))

@[expose] noncomputable def fixAllK : Bool :=
  fxIs zK 284 &&
    dcK.all (fun Y => !(eqK (mulV Y Y) IDP && !eqK Y IDP && !eqK Y zK) ||
      (fxIdx Y).isSome && (!fxIs Y 284 || (List.range 15).any (fun j => eqK Y (TP j)) ||
        fxIs (mulV Y zK) 52)) &&
    dcK.all fun B => !(!eqK (mulV B B) IDP && eqK (mulV (mulV B B) (mulV B B)) IDP) ||
      fxIs (mulV B B) 140

@[expose] noncomputable def a0K : Bool :=
  let A := wK LP glMkA0Word
  let N := mulV A A
  let C := wK LP glMkC1Word
  glMkWordOK glMkA0Word && glMkWordOK glMkC1Word && commK A zK && !eqK N IDP &&
    eqK (mulV N N) IDP && eqK (mulV C (mulV (TP 0) zK)) (mulV N C)

theorem fxBind_c0 : (((List.range (FXN 0)).drop (0 * 40)).take 40).all (fun j =>
    bindVK (KernelSporSch.Co2M.PV 0) (FXP j) (CFSG.KC.Co1F2.trK 22 (FXM j))) = true := by
  decide +kernel

theorem fxBind_c1 : (((List.range (FXN 0)).drop (1 * 40)).take 40).all (fun j =>
    bindVK (KernelSporSch.Co2M.PV 0) (FXP j) (CFSG.KC.Co1F2.trK 22 (FXM j))) = true := by
  decide +kernel

theorem fxBind_c2 : (((List.range (FXN 0)).drop (2 * 40)).take 40).all (fun j =>
    bindVK (KernelSporSch.Co2M.PV 0) (FXP j) (CFSG.KC.Co1F2.trK 22 (FXM j))) = true := by
  decide +kernel

theorem fxBind_c3 : (((List.range (FXN 0)).drop (3 * 40)).take 40).all (fun j =>
    bindVK (KernelSporSch.Co2M.PV 0) (FXP j) (CFSG.KC.Co1F2.trK 22 (FXM j))) = true := by
  decide +kernel

theorem fxBind_k : fxBindK = true := by
  rw [fxBindK, CFSG.KS.Raw.Orb.allN_eq]
  refine CFSG.KC.AllChunks.all_of_chunks _ _ 40 4 (by rw [List.length_range]; decide +kernel) ?_
  intro k hk
  match k, hk with
  | 0, _ => exact fxBind_c0
  | 1, _ => exact fxBind_c1
  | 2, _ => exact fxBind_c2
  | 3, _ => exact fxBind_c3
  | k + 4, h => exact absurd h (by omega)

theorem fixAll_k : fixAllK = true := by decide +kernel

theorem a0_k : a0K = true := by decide +kernel

end CertificateChecks.KernelCo2Smith
