module

public import Certificates.Data.CFSGNative.PropA.Check

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.M12Std.PropA.Native

@[noinline, expose] def centZOK (n : Nat) (xT j₁ j₂ : Table) (DL : Array Table) : Bool :=
  (DL.filter fun d => commP n j₁ d && commP n j₂ d).all fun d =>
    tblEq n d (idT n) || tblEq n d xT

@[expose] def ctxOK (n cap : Nat) (dD : DData) (dK : KData) : Bool :=
  let gD := dD.gens
  let giD := gD.map (invT n)
  let DL := mulClosureH n gD cap
  let xT := wordTab n gD giD dD.x
  let je := jEls n gD giD dD.jw
  let js := jGens n gD giD dD.jw
  let JL := mulClosureH n js cap
  let E := DL.1.filter (commP n xT)
  let tT := dK.gens[3]!
  gD.size == 2 && dK.gens.size == 4 && enumP n cap gD 95040 && enumP n cap dK.gens 380160 &&
    involP n xT && gensP n je && je.all (commP n xT) && enumP n cap js 60 &&
    commClosedOK n E JL.1 && E.size == 240 && centZOK n xT js[0]! js[1]! DL.1 &&
    involP n tT && dK.gens.all (commP n tT)

@[expose] def normalizesJ (n : Nat) (j₁ j₂ : Table) (JL : Array Table) (k : Table) : Bool :=
  memT n JL (conjT n k (invT n k) j₁) && memT n JL (conjT n k (invT n k) j₂)

@[noinline, expose] def scanNorm (n : Nat) (xT j₁ j₂ : Table) (JL KL : Array Table) : Bool :=
  KL.all fun k => invOK n k (invT n k) && (commP n xT k || !normalizesJ n j₁ j₂ JL k)

@[expose] def yAbelOK (n : Nat) (YL : Array Table) : Bool :=
  YL.all fun a => YL.all (commP n a)

@[expose] def yExpOK (n : Nat) (YL : Array Table) : Bool :=
  YL.all fun y => tblEq n (compT n (compT n y y) (compT n y y)) (idT n)

@[expose] def cyOK (n : Nat) (tT xT : Table) (HL YL : Array Table) : Bool :=
  (YL.filter fun y => HL.all (commP n y)).all fun y =>
    tblEq n y (idT n) || tblEq n y tT || tblEq n y xT || tblEq n y (compT n tT xT)

@[expose] def conjOK (n : Nat) (xT : Table) (HL YL : Array Table) : Bool :=
  YL.any fun o => HL.any fun m =>
    invOK n m (invT n m) && tblEq n (conjT n m (invT n m) o) (compT n o xT)

@[expose] def checkY (n cap : Nat) (dD : DData) (dK : KData) : Bool :=
  let gD := dD.gens
  let giD := gD.map (invT n)
  let xT := wordTab n gD giD dD.x
  let js := jGens n gD giD dD.jw
  let JL := mulClosureH n js cap
  let KL := mulClosureH n dK.gens cap
  let HL := KL.1.filter (commP n xT)
  let YL := HL.filter fun y => commP n js[0]! y && commP n js[1]! y
  ctxOK n cap dD dK && yAbelOK n YL && yExpOK n YL && scanNorm n xT js[0]! js[1]! JL.1 KL.1 &&
    jNormalOK n HL JL.1 && cyOK n dK.gens[3]! xT HL YL && conjOK n xT HL YL

@[expose] def cosetReps (n : Nat) (JL HL : Array Table) : Array Table := Id.run do
  let mut reps : Array Table := #[]
  for g in HL do
    if !(reps.any fun r => memT n JL (compT n (invT n r) g)) then
      reps := reps.push g
  return reps

@[expose] def repsOK (n : Nat) (HL reps : Array Table) : Bool :=
  reps.all fun r => invOK n r (invT n r) && memT n HL r

@[noinline, expose] def cosetCoverOK (n : Nat) (JL HL reps : Array Table) : Bool :=
  HL.all fun g => reps.any fun r => memT n JL (compT n (invT n r) g)

@[expose] def goodRep (n : Nat) (JL ws : Array Table) (r : Table) : Bool :=
  ws.any fun w => invOK n w (invT n w) && memT n JL (compT n (invT n w) r)

@[expose] def badRep (n cap : Nat) (j₁ j₂ xT : Table) (reps : Array Table) (r : Table) : Bool :=
  let gens := #[j₁, j₂, r] ++ reps.map fun c => conjT n c (invT n c) r
  let cl := mulClosureH n gens cap
  enumP n cap gens cl.1.size && memT n cl.1 xT

@[noinline, expose] def goodOrBadOK (n cap : Nat) (JL ws : Array Table) (j₁ j₂ xT : Table)
    (reps : Array Table) : Bool :=
  reps.all fun r => goodRep n JL ws r || badRep n cap j₁ j₂ xT reps r

@[expose] def checkN (n cap : Nat) (dD : DData) (dK : KData) : Bool :=
  let gD := dD.gens
  let giD := gD.map (invT n)
  let xT := wordTab n gD giD dD.x
  let js := jGens n gD giD dD.jw
  let JL := mulClosureH n js cap
  let KL := mulClosureH n dK.gens cap
  let tT := dK.gens[3]!
  let HL := KL.1.filter (commP n xT)
  let reps := cosetReps n JL.1 HL
  ctxOK n cap dD dK && repsOK n HL reps && cosetCoverOK n JL.1 HL reps &&
    goodOrBadOK n cap JL.1 #[idT n, tT, compT n tT xT] js[0]! js[1]! xT reps

@[expose] def isSqT (n : Nat) (tT T : Table) : Bool :=
  (tblEq n (compT n T T) (idT n) || tblEq n (compT n T T) tT) && !tblEq n T (idT n) &&
    !tblEq n T tT

@[expose] def orbitReps (n cap : Nat) (gD giD : Array Table) (tT : Table) (KL : Array Table) :
    Array Table := Id.run do
  let mut reps : Array Table := #[]
  let mut orbs : Array (Array Table) := #[]
  for w in KL do
    if isSqT n tT w && !(orbs.any fun o => memT n o w) then
      reps := reps.push w
      orbs := orbs.push (conjClosureH n gD giD w cap).1
  return reps

@[expose] def orbRepsOK (n cap : Nat) (gD giD reps : Array Table) : Bool :=
  reps.all fun r => permP n r &&
    (let o := conjClosureH n gD giD r cap
     conjTreeOK n gD giD r o.1 o.2.1 o.2.2)

@[noinline, expose] def coverP (n cap : Nat) (gD giD : Array Table) (tT : Table)
    (KL reps : Array Table) : Bool :=
  let orbs := reps.map fun r => conjClosureH n gD giD r cap
  KL.all fun T => !isSqT n tT T || orbs.any fun o => memT n o.1 T

@[expose] def commGens (n cap : Nat) (S : Array Table) : Array Table := Id.run do
  let mut gs : Array Table := #[]
  let mut cl : Array Table := #[idT n]
  for a in S do
    for b in S do
      let c := commutT n a b
      if !memT n cl c then
        gs := gs.push c
        cl := (mulClosureH n gs cap).1
  return gs

@[expose] def stopOK (n : Nat) (XL S : Array Table) : Bool :=
  S.size == 1 || XL.any fun x => S.all (commP n x)

@[expose] def chainOK (n cap : Nat) (XL : Array Table) : Nat → Array Table → Bool
  | 0, S => stopOK n XL S
  | fuel + 1, S =>
    stopOK n XL S ||
      (let gs := commGens n cap S
       let S' := mulClosureH n gs cap
       enumP n cap gs S'.1.size && commClosedOK n S S'.1 && chainOK n cap XL fuel S'.1)

@[noinline, expose] def chainsOK (n cap fuel : Nat) (XL DL reps : Array Table) : Bool :=
  reps.all fun r => chainOK n cap XL fuel (DL.filter (commP n r))

@[expose] def checkP (n cap fuel : Nat) (dD : DData) (dK : KData) : Bool :=
  let gD := dD.gens
  let giD := gD.map (invT n)
  let xT := wordTab n gD giD dD.x
  let js := jGens n gD giD dD.jw
  let JL := mulClosureH n js cap
  let DL := mulClosureH n gD cap
  let KL := mulClosureH n dK.gens cap
  let tT := dK.gens[3]!
  let sqs := JL.1.map fun s => compT n s s
  let XO := conjClosureH n gD giD xT cap
  let reps := orbitReps n cap gD giD tT KL.1
  ctxOK n cap dD dK && enumP n cap sqs 60 && conjTreeOK n gD giD xT XO.1 XO.2.1 XO.2.2 &&
    orbRepsOK n cap gD giD reps && coverP n cap gD giD tT KL.1 reps &&
    chainsOK n cap fuel XO.1 DL.1 reps

end CFSG.EvenSporadicStandard.M12Std.Rbc.Native
