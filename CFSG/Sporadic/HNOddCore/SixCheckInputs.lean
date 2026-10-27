module

public import CFSG.Sporadic.HNOddCore.SixData
public import CFSG.Sporadic.HNOddCore.SCheck
public import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNOddCore.SixData
public meta import CFSG.Sporadic.HNOddCore.SCheck
public meta import CFSG.Sporadic.HNSchreier.PrimCheck

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

@[expose] def om0L : Array Nat := InvData.o6Lists[1]!

@[expose] def om0Gens : Array (Array Nat) :=
  InvData.s6Perms.map fun s => restrictTab s om0L (posArr 8800 om0L)

@[expose] def dA (G : Array (Array Nat)) : Array Nat :=
  ppow 1100 (pword 1100 G (pinvs 1100 G) SixData.wa) SixData.ea

@[expose] def dB (G : Array (Array Nat)) : Array Nat :=
  ppow 1100 (pword 1100 G (pinvs 1100 G) SixData.wb) SixData.eb

@[expose] def dBaseArr : Array Nat := (SixData.dBase.map Fin.val).toArray

@[expose] def dLevels (a b : Array Nat) : Array Level :=
  rawLevels 1100 (strongArrs 1100 #[a, b] SixData.dWords) dBaseArr

@[expose] def dStab (a b : Array Nat) : Array (Array Nat) :=
  (strongArrs 1100 #[a, b] SixData.dWords).filter fun s => s[0]! == 0

@[expose] def subOrbits (H : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut seen : Array Bool := Array.replicate 1100 false
  let mut res : Array (Array Nat) := #[]
  for r in [0:1100] do
    if !seen[r]! then
      let L := bfsList 1100 H r
      for p in L do
        seen := seen.set! p true
      res := res.push L
  return res

@[expose] def subLabels (Ls : Array (Array Nat)) : Array Nat := Id.run do
  let mut lab : Array Nat := Array.replicate 1100 5
  for i in [0:Ls.size] do
    for p in Ls[i]! do
      lab := lab.set! p i
  return lab

@[noinline, expose] def sixChecksH (G : Array (Array Nat)) (a b : Array Nat) (lv : Array Level)
    (H Ls : Array (Array Nat)) (lab : Array Nat) : Bool :=
  G.size == 12 && (allBelowN 12 fun g => pisInv 1100 G[g]! (pinvCand 1100 G[g]!)) &&
    plettersOK 12 SixData.wa && plettersOK 12 SixData.wb &&
    peq 1100 (pcomp 1100 a a) (pid 1100) && !peq 1100 a (pid 1100) &&
    peq 1100 (ppow 1100 b 5) (pid 1100) && !peq 1100 b (pid 1100) &&
    peq 1100 (ppow 1100 (pcomp 1100 a b) 11) (pid 1100) && !peq 1100 (pcomp 1100 a b) (pid 1100) &&
    !peq 1100 (pcomp 1100 a b) (pcomp 1100 b a) &&
    chainCheck 1100 #[a, b] SixData.dWords SixData.dBase SixData.dSizes &&
    orbitOK 1100 #[a, b] (bfsList 1100 #[a, b] 0) && (bfsList 1100 #[a, b] 0).size == 1100 &&
    (allBelowN H.size fun i => (H[i]!)[0]! == 0 && pisInv 1100 H[i]! (pinvCand 1100 H[i]!) &&
      siftA 1100 lv dBaseArr 0 H[i]!) &&
    Ls.size == 5 && Ls.map Array.size == #[1, 336, 105, 630, 28] && (Ls[0]!)[0]! == 0 &&
    (allBelowN 5 fun i => orbitOK 1100 H Ls[i]!) && lab.size == 1100 &&
    (allBelowN 5 fun i => allBelowN (Ls[i]!).size fun k => lab[(Ls[i]!)[k]!]! == i) &&
    (allBelowN 1100 fun p => decide (lab[p]! < 5) && (Ls[lab[p]!]!).contains p) &&
    (allBelowN 12 fun g =>
      siftA 1100 lv dBaseArr 0 (pcomp 1100 G[g]! (pcomp 1100 a (pinvCand 1100 G[g]!))) &&
      siftA 1100 lv dBaseArr 0 (pcomp 1100 G[g]! (pcomp 1100 b (pinvCand 1100 G[g]!)))) &&
    !siftA 1100 lv dBaseArr 0 G[5]!

@[noinline, expose] def sixChecksD (G : Array (Array Nat)) (a b : Array Nat)
    (H : Array (Array Nat)) (Ls : Array (Array Nat)) : Bool :=
  sixChecksH G a b (dLevels a b) H Ls (subLabels Ls)

@[noinline, expose] def sixChecksA (G : Array (Array Nat)) (a b : Array Nat) : Bool :=
  sixChecksD G a b (dStab a b) (subOrbits (dStab a b))

@[noinline, expose] def sixChecks : Bool := sixChecksA om0Gens (dA om0Gens) (dB om0Gens)

end CFSG.Sporadic.HNOddCore.Native
