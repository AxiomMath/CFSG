module

public import CFSG.RankThree.Native.ONSevenData
public import CFSG.Sporadic.Schreier.ONGlue
public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.Monster.B.Mathieu.SylowCore
public import CFSG.Sporadic.Schreier.ONCheckChainInputs
public import Certificates.Data.CFSGNative.ONSchreier.Tools

public section

namespace CFSG.RankThree.Native

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer

@[expose] def onSevenInvArrs : Array (Array Nat) := pinvs nPts qonStrongArrs

@[expose] def onSevenArr (w : List Int) : Array Nat := pword nPts qonStrongArrs onSevenInvArrs w

@[expose] def onSevenPow (x : Array Nat) : Nat → Array Nat
  | 0 => pid nPts
  | e + 1 => pcomp nPts x (onSevenPow x e)

@[expose] def onSevenConj (t x : Array Nat) : Array Nat :=
  pcomp nPts (pcomp nPts t x) (pinvCand nPts t)

@[expose] def onSevenConjInv (u x : Array Nat) : Array Nat :=
  pcomp nPts (pcomp nPts (pinvCand nPts u) x) u

@[expose] def onSevenLineArrs : Array (Array Nat) := onSevenLineWords.map onSevenArr

@[expose] def onSevenQArrs : Array (Array Nat) := onSevenSylowWords.map onSevenArr

@[expose] def onSevenCArrs (r : Nat) : Array (Array Nat) := onSevenCentWords[r]!.map onSevenArr

@[expose] def onSevenFArrs (r : Nat) : Array (Array Nat) := onSevenNormalWords[r]!.map onSevenArr

@[expose] def onSevenRepArr (r : Nat) : Array Nat := onSevenLineArrs[onSevenRepIdx[r]!]!

@[expose] def onSevenBase : Array Nat := #[0, 227759, 100817]

@[expose] def onSevenOrbit (gs : Array (Array Nat)) : Array Nat := Id.run do
  let mut pts : Array Nat := onSevenBase
  let mut seen : Std.HashMap Nat Nat :=
    (((∅ : Std.HashMap Nat Nat).insert 0 0).insert 227759 1).insert 100817 2
  for h in [0:nPts] do
    if h < pts.size then
      for g in gs do
        let y := g[pts[h]!]!
        if !seen.contains y then
          seen := seen.insert y pts.size
          pts := pts.push y
    else break
  return pts

@[expose] def onSevenTab (R g : Array Nat) : Array Nat := restrictTab g R (posArr nPts R)

@[expose] def onSevenResOK (R : Array Nat) (gs : Array (Array Nat)) : Bool :=
  pointsOK nPts R (posArr nPts R) && decide (3 ≤ R.size) && R[0]! == 0 && R[1]! == 227759 &&
    R[2]! == 100817 && allBelowN gs.size fun k => restrictOK gs[k]! R (onSevenTab R gs[k]!)

@[expose] def onSevenKeys : List Nat := [0, 1, 2]

@[expose] def onSevenQR : Array Nat := onSevenOrbit onSevenQArrs

@[expose] def onSevenQTabs : Array (Array Nat) := onSevenQArrs.map (onSevenTab onSevenQR)

@[expose] def onSevenLineTabs : Array (Array Nat) := onSevenLineArrs.map (onSevenTab onSevenQR)

@[expose] def onSevenQCert : ArrCert := enumBfs onSevenQR.size onSevenQTabs onSevenKeys 400

@[expose] def onSevenQCheck (R : Array Nat) (ts lt : Array (Array Nat)) (c : ArrCert) : Bool :=
  onSevenResOK R (onSevenQArrs ++ onSevenLineArrs) && enumOK R.size ts onSevenKeys c &&
    c.pts.size == 343 && lt.size == 57 &&
    allLt 343 (fun k => eqA R.size (powArr R.size c.pts[k]! 7) (idA R.size)) &&
    allLt 343 (fun k => eqA R.size c.pts[k]! (idA R.size) ||
      (List.range 57).any fun j => (List.range 7).any fun e =>
        eqA R.size c.pts[k]! (powArr R.size lt[j]! e)) &&
    allLt 57 (fun j => allLt 57 fun j' => j == j' ||
      allLt 7 fun e => !(eqA R.size lt[j]! (powArr R.size lt[j']! e))) &&
    allLt 57 (fun j => validA R.size lt[j]! && eqA R.size (powArr R.size lt[j]! 7) (idA R.size) &&
      !(eqA R.size lt[j]! (idA R.size)) && c.pts.toList.any (eqA R.size lt[j]!))

@[expose] def onSevenCR (r : Nat) : Array Nat := onSevenOrbit (onSevenCArrs r)

@[expose] def onSevenCTabs (r : Nat) : Array (Array Nat) :=
  (onSevenCArrs r).map (onSevenTab (onSevenCR r))

@[expose] def onSevenFTabs (r : Nat) : Array (Array Nat) :=
  (onSevenFArrs r).map (onSevenTab (onSevenCR r))

@[expose] def onSevenRepTab (r : Nat) : Array Nat := onSevenTab (onSevenCR r) (onSevenRepArr r)

@[expose] def onSevenCCert (r : Nat) : ArrCert :=
  enumBfs (onSevenCR r).size (onSevenCTabs r) onSevenKeys 1400

@[expose] def onSevenFCert (r : Nat) : ArrCert :=
  enumBfs (onSevenCR r).size (onSevenFTabs r) onSevenKeys 400

@[expose] def onSevenCCheck (R x : Array Nat) (cs ts : Array (Array Nat)) (c : ArrCert)
    (sz : Nat) : Bool :=
  onSevenResOK R (cs.push x) &&
    allBelowN cs.size (fun k => peq nPts (pcomp nPts cs[k]! x) (pcomp nPts x cs[k]!)) &&
    enumOK R.size ts onSevenKeys c && c.pts.size == sz

@[expose] def onSevenFCheck (R : Array Nat) (ts : Array (Array Nat)) (cC : ArrCert)
    (fs tf : Array (Array Nat)) (tx : Array Nat) (cF : ArrCert) : Bool :=
  onSevenResOK R fs && enumOK R.size tf onSevenKeys cF && cF.pts.size == 343 &&
    allLt tf.size (fun l => cC.pts.toList.any (eqA R.size tf[l]!)) &&
    allLt ts.size (fun k => allLt tf.size fun l =>
      cF.pts.toList.any (eqA R.size (conjA R.size ts[k]! tf[l]!))) &&
    cF.pts.toList.any (eqA R.size tx) &&
    allLt cC.pts.size (fun k => !(allLt tf.size fun l => commA R.size cC.pts[k]! tf[l]!) ||
      (List.range 7).any fun e => eqA R.size cC.pts[k]! (powArr R.size tx e))

abbrev onSevenLevels : Array CLevel :=
  cLevels nPts Data.baseList.toArray
    (allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray)

abbrev onSevenSteps : Array (Array (Array Nat)) :=
  allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray

@[expose] def onSevenCount (x : Array Nat) : Nat :=
  commCount onSevenLevels onSevenSteps 1 2 x onSevenBase

@[expose] def onSevenGood (x : Array Nat) (bad : List Nat) : List Nat :=
  (List.range nPts).filter fun q => x[q]! == q && !(bad.contains q)

@[expose] def onSevenCosetTestAt (L : Array CLevel) (St : Array (Array (Array Nat)))
    (u x : Array Nat) (k₁ k₂ : Nat) : Bool :=
  onSevenBase.all fun p => u[tr2App L St 1 2 k₁ k₂ x[p]!]! == x[u[tr2App L St 1 2 k₁ k₂ p]!]!

@[expose] def onSevenCosetFreeAt (L : Array CLevel) (St : Array (Array (Array Nat)))
    (u x : Array Nat) : Bool :=
  allBelowN 52136 fun k₁ => allBelowN 36 fun k₂ => !(onSevenCosetTestAt L St u x k₁ k₂)

@[expose] def onSevenCosetFree (u x : Array Nat) : Bool :=
  onSevenCosetFreeAt onSevenLevels onSevenSteps u x

@[expose] def onSevenConjArr (r : Nat) : Array Nat :=
  onSevenConj (onSevenArr onSevenConjWords[r]!) (onSevenRepArr r)

@[expose] def onSevenBoundCheck (r : Nat) (xp : Array Nat) (c good : Nat) (useScan : Bool) :
    Bool :=
  pisInv nPts (onSevenArr onSevenConjWords[r]!) (pinvCand nPts (onSevenArr onSevenConjWords[r]!)) &&
    xp[0]! == 0 && onSevenCount xp == c &&
    (onSevenGood xp (onSevenBadData[r]!.toList.map Prod.fst)).length == good &&
    allBelowN onSevenBadData[r]!.size fun i =>
      (onSevenArr (onSevenBadData[r]!)[i]!.2)[0]! == (onSevenBadData[r]!)[i]!.1 &&
        pisInv nPts (onSevenArr (onSevenBadData[r]!)[i]!.2)
          (pinvCand nPts (onSevenArr (onSevenBadData[r]!)[i]!.2)) &&
        (if useScan then onSevenCosetFree (onSevenArr (onSevenBadData[r]!)[i]!.2) xp
        else onSevenCount (onSevenConjInv (onSevenArr (onSevenBadData[r]!)[i]!.2) xp) != c)

@[expose] def onSevenTransCheck (r : Nat) : Bool :=
  onSevenTransporterData[r]!.all fun t =>
    decide (1 ≤ t.power) && decide (t.power ≤ 6) && decide (t.line < 57) &&
      peq nPts (pcomp nPts (onSevenArr t.word) (onSevenPow (onSevenRepArr r) t.power))
        (pcomp nPts onSevenLineArrs[t.line]! (onSevenArr t.word))

@[expose] def onSevenZArr : Array Nat :=
  pcomp nPts (pcomp nPts (pcomp nPts onSevenQArrs[0]! onSevenQArrs[1]!)
    (pinvCand nPts onSevenQArrs[0]!)) (pinvCand nPts onSevenQArrs[1]!)

@[expose] def onSevenHArr : Array Nat := (onSevenCArrs 0)[2]!

@[expose] def onSevenKernelCheck : Bool :=
  pisInv nPts onSevenQArrs[0]! (pinvCand nPts onSevenQArrs[0]!) &&
    pisInv nPts onSevenQArrs[1]! (pinvCand nPts onSevenQArrs[1]!) &&
    pisInv nPts onSevenHArr (pinvCand nPts onSevenHArr) &&
    !(peq nPts onSevenZArr (pid nPts)) &&
    peq nPts (pcomp nPts onSevenZArr onSevenQArrs[0]!) (pcomp nPts onSevenQArrs[0]! onSevenZArr) &&
    peq nPts (pcomp nPts onSevenZArr onSevenQArrs[1]!) (pcomp nPts onSevenQArrs[1]! onSevenZArr) &&
    peq nPts (onSevenConj onSevenHArr onSevenQArrs[0]!)
      (pcomp nPts (pcomp nPts (onSevenPow onSevenQArrs[0]! 6) (onSevenPow onSevenQArrs[1]! 0))
        (onSevenPow onSevenZArr 3)) &&
    peq nPts (onSevenConj onSevenHArr onSevenQArrs[1]!)
      (pcomp nPts (pcomp nPts (onSevenPow onSevenQArrs[0]! 0) (onSevenPow onSevenQArrs[1]! 6))
        (onSevenPow onSevenZArr 2)) &&
    peq nPts (onSevenConj onSevenHArr onSevenZArr) (onSevenPow onSevenZArr 1)

end CFSG.RankThree.Native
