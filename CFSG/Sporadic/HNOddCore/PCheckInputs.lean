module

public import CFSG.Sporadic.HNOddCore.QCheck
public import Std.Data.HashMap
public meta import CFSG.Sporadic.HNOddCore.QCheck
public meta import Std.Data.HashMap

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native

@[expose] def pWords : Array (List Int) := QData.qFlat ++ InvData.pLiftWords

@[expose] def pparOf (par : Array (List Int)) (k : Nat) : Nat := ((par[k]!).getD 0 0).toNat

@[expose] def plabOf (par : Array (List Int)) (k : Nat) : Nat := ((par[k]!).getD 1 0).toNat

@[expose] def pEnum (pg : Array (Array Nat)) (par : Array (List Int)) : Array (Array Nat) :=
  Id.run do
    let mut E : Array (Array Nat) := #[pid 800]
    for k in [1:par.size] do
      E := E.push (pcomp 800 pg[plabOf par k]! E[pparOf par k]!)
    return E

@[expose] def pIdx (E : Array (Array Nat)) : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for k in [0:E.size] do
    m := m.insert E[k]! k
  return m

@[expose] def pconj (g gi x : Array Nat) : Array Nat := pcomp 800 g (pcomp 800 x gi)

@[expose] def conjOrbit (idx : Std.HashMap (Array Nat) Nat) (E pg pgi : Array (Array Nat))
    (r : Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let mut L : Array Nat := #[r]
  let mut par : Array Nat := #[0]
  let mut gen : Array Nat := #[0]
  let mut seen : Array Bool := (Array.replicate 16384 false).set! r true
  for i in [0:16384] do
    if i < L.size then
      for g in [0:pg.size] do
        let m := idx.getD (pconj pg[g]! pgi[g]! E[L[i]!]!) 16384
        if m < 16384 && !seen[m]! then
          seen := seen.set! m true
          L := L.push m
          par := par.push i
          gen := gen.push g
  return (L, par, gen)

@[expose] def classMarks (Ls : Array (Array Nat)) : Array Nat := Id.run do
  let mut mk : Array Nat := Array.replicate 16384 29
  for c in [0:Ls.size] do
    for k in Ls[c]! do
      mk := mk.set! k c
  return mk

@[expose] def classOK (idx : Std.HashMap (Array Nat) Nat) (E pg pgi : Array (Array Nat)) (r : Nat)
    (L tpar tgen : Array Nat) : Bool :=
  L.size ≤ 16384 && decide (0 < L.size) && L[0]! == r && tpar.size == L.size &&
    tgen.size == L.size &&
    (allBelowN L.size fun j => decide (L[j]! < 16384) &&
      (j == 0 || (decide (tpar[j]! < j) && decide (tgen[j]! < 14) &&
        peq 800 E[L[j]!]! (pconj pg[tgen[j]!]! pgi[tgen[j]!]! E[L[tpar[j]!]!]!)))) &&
    (allBelowN L.size fun j => allBelowN 14 fun g =>
      let m := idx.getD (pconj pg[g]! pgi[g]! E[L[j]!]!) 16384
      decide (m < 16384) && peq 800 E[m]! (pconj pg[g]! pgi[g]! E[L[j]!]!) &&
        L.contains m)

@[noinline, expose] def sylowChecksH (S pg : Array (Array Nat)) (par : Array (List Int))
    (E left : Array (Array Nat)) (reps : Array Nat)
    (cs : Array (Array Nat × Array Nat × Array Nat)) (mk : Array Nat) : Bool :=
  let Si := pinvs 800 S
  let pgi := pinvs 800 pg
  let idx := pIdx E
  S.size == 11 && pg.size == 14 && pWords.size == 14 &&
    (allBelowN 14 fun i =>
      plettersOK 11 pWords[i]! && peq 800 (pword 800 S Si pWords[i]!) pg[i]! &&
        pisInv 800 pg[i]! pgi[i]!) &&
    par.size == 16384 && E.size == 16384 && peq 800 E[0]! (pid 800) &&
    (allBelowN 16384 fun k => k == 0 || (decide (pparOf par k < k) && decide (plabOf par k < 14) &&
      peq 800 E[k]! (pcomp 800 pg[plabOf par k]! E[pparOf par k]!))) &&
    left.size == 14 &&
    (allBelowN 14 fun g => allBelowN 16384 fun k =>
      decide ((left[g]!)[k]! < 16384) && peq 800 (pcomp 800 pg[g]! E[k]!) E[(left[g]!)[k]!]!) &&
    chainCheck 800 pg QData.pbarWords QData.pbarBase QData.pbarSizes &&
    (List.range 16384).countP (fun k => peq 800 (pcomp 800 E[k]! E[k]!) (pid 800)) == 880 &&
    reps.size == 29 && cs.size == 29 && mk.size == 16384 &&
    (allBelowN 29 fun c => peq 800 (pcomp 800 E[reps[c]!]! E[reps[c]!]!) (pid 800) &&
      classOK idx E pg pgi reps[c]! cs[c]!.1 cs[c]!.2.1 cs[c]!.2.2) &&
    (allBelowN 29 fun c => allBelowN 29 fun c' => c == c' || !(cs[c']!.1.contains reps[c]!)) &&
    (allBelowN 16384 fun k => !peq 800 (pcomp 800 E[k]! E[k]!) (pid 800) ||
      (decide (mk[k]! < 29) && cs[mk[k]!]!.1.contains k))

@[expose] def pReps : Array Nat := InvData.clsLists.map fun L => L[0]!

@[noinline, expose] def sylowChecksE (S pg : Array (Array Nat)) (par : Array (List Int))
    (E : Array (Array Nat)) : Bool :=
  let pgi := pinvs 800 pg
  let idx := pIdx E
  let cs := pReps.map fun r => conjOrbit idx E pg pgi r
  sylowChecksH S pg par E InvData.pleftTabs pReps cs (classMarks (cs.map (·.1)))

@[noinline, expose] def sylowChecks : Bool :=
  sylowChecksE InvData.s4Perms InvData.pgenPerms InvData.parRecs
    (pEnum InvData.pgenPerms InvData.parRecs)

end CFSG.Sporadic.HNOddCore.Native
