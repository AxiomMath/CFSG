module

public import Certificates.Data.Kernel.YoshQ.TabN
public import Certificates.Data.AE6CertF

public section

namespace CFSG.KC.AE6F

open CFSG.KC.Enum CFSG.KC.YoshQ Certificates.AE6Model

@[expose] noncomputable def awN (G : List Nat) (w : List Nat) : Nat :=
  w.foldr (fun i acc => pmN 360 9 (G.getD i (pidn 360 9)) acc) (pidn 360 9)

@[expose] noncomputable def commN (x y : Nat) : Bool := eqN 360 9 (pmN 360 9 x y) (pmN 360 9 y x)

@[expose] noncomputable def memN (L : List Nat) (x : Nat) : Bool := L.any fun t => eqN 360 9 x t

@[expose] noncomputable def conjN (g gi x : Nat) : Nat := pmN 360 9 (pmN 360 9 g x) gi

@[expose] noncomputable def spanQN (R Y : Nat) : List Nat :=
  let R2 := pmN 360 9 R R
  [pidn 360 9, R2, R, pmN 360 9 R R2, Y, pmN 360 9 Y R2, pmN 360 9 R Y, pmN 360 9 Y R]

@[expose] noncomputable def evalHN (HT : List (Nat × Nat)) (w : List Nat) : Nat :=
  w.foldl (fun acc k => pmN 360 9 acc
    (if k % 2 = 0 then (HT.getD (k / 2) (pidn 360 9, pidn 360 9)).1
      else (HT.getD (k / 2) (pidn 360 9, pidn 360 9)).2)) (pidn 360 9)

@[expose] noncomputable def fBasicN (G : List Nat) : Bool :=
  let Z := awN G zWord
  let K0 := awN G (fKWordsN.getD 0 [])
  let K1 := awN G (fKWordsN.getD 1 [])
  (fKWordsN.all fun w => let k := awN G w; eqN 360 9 (pmN 360 9 k k) Z) &&
    !eqN 360 9 Z (pidn 360 9) && eqN 360 9 (pmN 360 9 Z Z) (pidn 360 9) &&
    eqN 360 9 (pmN 360 9 (pmN 360 9 K1 K0) (pmN 360 9 K0 K1)) (pidn 360 9) &&
    G.all fun g => eqN 360 9 (pmN 360 9 g g) (pidn 360 9)

@[expose] noncomputable def fTwinPairsN (G : List Nat) : List (Nat × Nat) :=
  let x := awN G (fKWordsN.getD 0 [])
  let y := awN G (fKWordsN.getD 1 [])
  fTwinWordsN.map fun w => let c := awN G w;
    (pmN 360 9 (pmN 360 9 c x) (invN 360 9 c), pmN 360 9 (pmN 360 9 c y) (invN 360 9 c))

@[expose] noncomputable def fTwinChecksN (G : List Nat) : Bool :=
  let TP := fTwinPairsN G
  let TS := TP.map fun p => spanQN p.1 p.2
  fCLettersN.all fun l =>
    let Gt := G.getD l (pidn 360 9)
    let Gi := invN 360 9 Gt
    TP.all fun p => TS.any fun sp => memN sp (conjN Gt Gi p.1) && memN sp (conjN Gt Gi p.2)

@[expose] noncomputable def fCycTabsN (G : List Nat) : List (Nat × Nat) :=
  (List.range 12).map fun m => (awN G (fCycWordN m), invN 360 9 (awN G (fCycWordN m)))

@[expose] noncomputable def fCycChecksN (G : List Nat) : Bool :=
  let CT := fCycTabsN G
  (List.range 12).all (fun m => (List.range 12).all fun n =>
    let gm := CT.getD m (pidn 360 9, pidn 360 9)
    let gn := CT.getD n (pidn 360 9, pidn 360 9)
    (m == n || (!eqN 360 9 gm.1 gn.1 && !eqN 360 9 gm.1 gn.2)) &&
      (m / 3 == n / 3 || commN gm.1 gn.1) &&
      (m / 3 != n / 3 || m == n || eqN 360 9 (pmN 360 9 (pmN 360 9 gm.1 gn.1) gm.2) gn.2)) &&
    (List.range 7).all fun x =>
      let a := G.getD (fCLettersN.getD x 0) (pidn 360 9)
      (List.range 12).all fun m =>
        let t := CT.getD ((fLetterHat.getD x []).getD m 0) (pidn 360 9, pidn 360 9)
        let v := pmN 360 9 (pmN 360 9 a (CT.getD m (pidn 360 9, pidn 360 9)).1) a
        eqN 360 9 v t.1 || eqN 360 9 v t.2

@[expose] noncomputable def fDiagChecksN (G WL : List Nat) : Bool :=
  let Z := awN G zWord
  let CT := fCycTabsN G
  (List.range 2).all fun c =>
    let d := fDiagN.getD c []
    let gh := fGammaHat.getD c []
    let HT := (List.range 8).map fun i =>
      let g := G.getD (d.getD i 0) (pidn 360 9)
      (g, invN 360 9 g)
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6.curtisRels.all
        (fun r => eqN 360 9 (evalHN HT r) (pidn 360 9)) &&
      eqN 360 9 (awN G (zWord.map fun i => d.getD i 0)) Z &&
      ((List.range 12).all fun m =>
        let t := CT.getD (gh.getD m 0) (pidn 360 9, pidn 360 9)
        let v := awN G ((fCycWordN m).map fun i => d.getD i 0)
        eqN 360 9 v t.1 || eqN 360 9 v t.2) &&
      wWords.all fun w => memN WL (awN G (w.map fun i => d.getD i 0))

end CFSG.KC.AE6F

end
