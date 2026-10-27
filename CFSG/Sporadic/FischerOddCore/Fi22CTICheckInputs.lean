module

public import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public import Certificates.Kernel.Sporadic.Fi22.C3151
public import Certificates.Kernel.Sporadic.Fi22.C2068

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def ctiG (k : Nat) : Array Nat := fi22CentArr (19 + k)

@[expose] def ctiGi (k : Nat) : Array Nat := invCand 3510 (ctiG k)

@[expose] def ctiQ3 : Array Nat := Native.powA 3510 (compA 3510 (ctiG 2) (ctiG 6)) 6

@[expose] def ctiQ7 : Array Nat := Native.powA 3510 (compA 3510 (ctiG 6) (ctiG 8)) 4

@[expose] def ctiQF (i : Fin 10) : Array Nat :=
  match i.val with
  | 0 => ctiG 0
  | 1 => Native.powA 3510 (compA 3510 (ctiG 1) (ctiG 7)) 9
  | 2 => ctiQ3
  | 3 => Native.powA 3510 (compA 3510 (ctiG 3) (ctiG 8)) 4
  | 4 => Native.powA 3510 (compA 3510 (ctiG 4) (ctiG 7)) 4
  | 5 => Native.powA 3510 (compA 3510 (ctiG 5) (ctiG 6)) 2
  | 6 => ctiQ7
  | 7 => conjArr 3510 (ctiG 1) (ctiGi 1) ctiQ3
  | 8 => conjArr 3510 (ctiG 3) (ctiGi 3) ctiQ3
  | _ => conjArr 3510 (ctiG 4) (ctiGi 4) ctiQ3

@[expose] def ctiQArr : Array (Array Nat) := Array.ofFn ctiQF

@[expose] def ctiZ : Array Nat :=
  compA 3510 ctiQArr[6]! (compA 3510 ctiQArr[2]! (compA 3510 (invCand 3510 ctiQArr[6]!)
    (invCand 3510 ctiQArr[2]!)))

@[expose] def ctiMem (E : Array (Array Nat)) (x : Array Nat) : Bool :=
  E.any fun e => eqA 3510 e x

@[expose] def ctiInCoset (E : Array (Array Nat)) (z x : Array Nat) (r : Nat) : Bool :=
  eqA 3510 x E[r]! || eqA 3510 x (compA 3510 E[r]! z)

@[expose] def ctiCosets (E : Array (Array Nat)) (z : Array Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut idx : Std.HashMap (Array Nat) Nat := {}
  for i in [0:E.size] do
    idx := idx.insert E[i]! i
  let zi := E.map fun e => (idx[compA 3510 e z]?).getD E.size
  let mut cid : Array Nat := Array.replicate E.size 0
  let mut seen : Array Bool := Array.replicate E.size false
  let mut reps : Array Nat := #[]
  for i in [0:E.size] do
    if !seen[i]! then
      cid := (cid.set! i reps.size).set! zi[i]! reps.size
      seen := (seen.set! i true).set! zi[i]! true
      reps := reps.push i
  return (cid, reps, zi)

@[expose] def ctiPi (E : Array (Array Nat)) (cid reps g gi : Array Nat) : Array Nat := Id.run do
  let mut idx : Std.HashMap (Array Nat) Nat := {}
  for i in [0:E.size] do
    idx := idx.insert E[i]! i
  return reps.map fun r => cid[(idx[conjArr 3510 g gi E[r]!]?).getD 0]!

@[expose] def ctiQOK (E : Array (Array Nat)) (par gen nxt cid reps zi : Array Nat)
    (πs : Array (Array Nat)) : Bool :=
  closureOK 3510 ctiQArr E par gen nxt && E.size == 1024 &&
    keysOK 3510 [0, 1, 2, 3, 6, 4] E &&
    allLt 10 (fun j => siftA 3510 (rawLevels 3510 (fi22CentStrong 1) #[0, 1, 2, 3, 6, 4])
      #[0, 1, 2, 3, 6, 4] 0 ctiQArr[j]!) &&
    allLt 9 (fun k => allLt 10 fun j => ctiMem E (conjArr 3510 (ctiG k) (ctiGi k) ctiQArr[j]!)) &&
    !(eqA 3510 ctiZ (idA 3510)) && eqA 3510 (compA 3510 ctiZ ctiZ) (idA 3510) &&
    allLt 9 (fun k => eqA 3510 (compA 3510 (ctiG k) ctiZ) (compA 3510 ctiZ (ctiG k))) &&
    reps.size == 512 && πs.size == 9 &&
    allLt 512 (fun c => decide (reps[c]! < 1024) && cid[reps[c]!]! == c) &&
    allLt 1024 (fun i => decide (cid[i]! < 512) && decide (zi[i]! < 1024) &&
      eqA 3510 E[zi[i]!]! (compA 3510 E[i]! ctiZ) && cid[zi[i]!]! == cid[i]! &&
      ctiInCoset E ctiZ E[i]! reps[cid[i]!]!) &&
    allLt 10 (fun j => allLt 512 fun c =>
      eqA 3510 (compA 3510 ctiQArr[j]! E[reps[c]!]!) (compA 3510 E[reps[c]!]! ctiQArr[j]!) ||
        eqA 3510 (compA 3510 ctiQArr[j]! E[reps[c]!]!)
          (compA 3510 (compA 3510 E[reps[c]!]! ctiZ) ctiQArr[j]!)) &&
    allLt 9 (fun k => πs[k]!.size == 512 && allLt 512 fun c => decide ((πs[k]!)[c]! < 512) &&
      ctiInCoset E ctiZ (conjArr 3510 (ctiG k) (ctiGi k) E[reps[c]!]!) reps[(πs[k]!)[c]!]!) &&
    allLt 10 (fun j => isInvA 3510 ctiQArr[j]! (invCand 3510 ctiQArr[j]!))

@[expose] def ctiImageOK (πs E5 : Array (Array Nat)) (par gen nxt : Array Nat) : Bool :=
  closureOK 512 πs E5 par gen nxt && E5.size == 51840 && keysOK 512 [18, 32, 2] E5

@[expose] def ctiChecks : Bool :=
  let r := closureSearch 3510 ctiQArr 1100
  let cd := ctiCosets r.1 ctiZ
  let πs := (List.range 9).toArray.map fun k => ctiPi r.1 cd.1 cd.2.1 (ctiG k) (ctiGi k)
  let r5 := closureSearch 512 πs 60000
  ctiQOK r.1 r.2.1 r.2.2.1 r.2.2.2 cd.1 cd.2.1 cd.2.2 πs &&
    ctiImageOK πs r5.1 r5.2.1 r5.2.2.1 r5.2.2.2

end CFSG.Sporadic.FischerOddCore
