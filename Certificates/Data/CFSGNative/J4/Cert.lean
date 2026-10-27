module

public import Certificates.Data.CFSGNative.J4.Data
public import Certificates.Data.CFSGNative.J4.Global
public import Certificates.Data.CFSGNative.J4.Faithful
public import Certificates.Data.CFSGNative.J4.Suborbits
public import Certificates.Data.CFSGNative.J4.Chain
public import Certificates.Data.CFSGNative.J4.Local

public section

namespace CFSG.Sporadic.J4.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def rowsA (_ : Unit := ()) : Array V2 := rowsOf seedA

@[expose] def rowsB (_ : Unit := ()) : Array V2 := rowsOf seedB

@[expose] def baseMats (_ : Unit := ()) : Array (Array V2) := #[rowsA, rowsB]

@[expose] def baseInvs (_ : Unit := ()) : Array (Array V2) := baseMats.map invRows

@[expose] def locMats (_ : Unit) : Array (Array V2) :=
  localWords.toArray.map (wordRows baseMats baseInvs)

@[expose] def locInvs (_ : Unit) : Array (Array V2) := (locMats ()).map invRows

@[expose] def stabMats (_ : Unit) : Array (Array V2) :=
  stabWords.toArray.map (wordRows (locMats ()) (locInvs ()))

@[expose] def conjRows (_ : Unit := ()) : Array V2 := wordRows baseMats baseInvs conjWord

@[expose] def zRows (_ : Unit := ()) : Array V2 :=
  mulRows (mulRows (mulRows rowsA (invRows conjRows)) (mulRows rowsA rowsB)) conjRows

@[expose] def matChecks (_ : Unit := ()) : Bool :=
  let A := rowsA
  let B := rowsB
  let AB := mulRows A B
  invsOK baseMats baseInvs && invsOK (locMats ()) (locInvs ()) && (locMats ()).size == 3 &&
    (stabMats ()).size == 6 &&
    (locMats ()).all (fun M => (frApply (frTable M) rootV).beq rootV) &&
    eqRows (powRows A 2) idRows && !eqRows A idRows &&
    eqRows (powRows B 4) idRows && !eqRows (powRows B 2) idRows &&
    eqRows (powRows AB 37) idRows && !eqRows AB idRows &&
    eqRows (mulRows conjRows (invRows conjRows)) idRows &&
    eqRows (powRows zRows 43) idRows && !eqRows zRows idRows &&
    eqRows (mulRows (mulRows A formRows) (transposeRows A)) formRows &&
    eqRows (mulRows (mulRows B formRows) (transposeRows B)) formRows

@[expose] def pointsOfDepth (n : Nat) (dep : ByteArray) (d : Nat) : Array Nat := Id.run do
  let mut r : Array Nat := #[]
  for j in [0:n] do
    if depOf dep j == d then r := r.push j
  return r

@[expose] def stLabel (n : Nat) (z0 z1 z2 : ByteArray) (chunks : Nat) : Bool :=
  let L := labelPar n z0 z1 z2 subReps subSizes.toArray labelGroups
  labelOK n z0 z1 z2 L chunks && L.reps == subReps && (countLab n 7 L).toList == subSizes

@[inline, expose] def invLetter (ta tb tbi : ByteArray) (l : Nat) : ByteArray := letter3 ta tbi tb l

@[expose] def mkPairs (n : Nat) (ta tb tbi : ByteArray) (chunks : Nat) : Array ByteArray :=
  pairLetters.map fun (l1, l2) =>
    compTab n (invLetter ta tb tbi l2) (invLetter ta tb tbi l1) chunks

@[expose] def pairsOK (n : Nat) (ta tb tbi : ByteArray) (pairs : Array ByteArray) (chunks : Nat) :
    Bool :=
  pairs.size == 6 && (List.range 6).all fun k =>
    compOK n pairs[k]! (invLetter ta tb tbi pairLetters[k]!.2)
      (invLetter ta tb tbi pairLetters[k]!.1) chunks

structure StoreOut where
  tbi : ByteArray
  z0 : ByteArray
  z1 : ByteArray
  z2 : ByteArray
  q0 : Array Nat
  lev : Level
  tup : Array (Array Nat)
  tmap : Std.HashMap (Array Nat) Nat

@[expose] def stGlobal (n : Nat) (ta tb : ByteArray) (S : StoreOut) (par2 dep2 : ByteArray)
    (chunks : Nat) : Bool :=
  let pairs := mkPairs n ta tb S.tbi chunks
  if !pairsOK n ta tb S.tbi pairs chunks then false else
  let cpts := pointsOfDepth n dep2 cacheDepth
  let GD : GData := ⟨n, ta, tb, S.tbi, par2, dep2, S.q0, S.lev, qLen, S.tup, S.tmap, cacheDepth,
    NatMap.ofKeys cpts 21, mkCache par2 ta tb S.tbi S.q0 cpts, pairs⟩
  globalOK GD chunks

@[noinline, expose] def treeGlobal (n : Nat) (ta tb : ByteArray) (S : StoreOut) (lok : Bool)
    (tt : Task (ByteArray × ByteArray)) (chunks : Nat) : Bool :=
  if !lok then false else
  let t2 := tt.get
  if !treeOK n ta tb S.tbi t2.1 t2.2 chunks then false else
  stGlobal n ta tb S t2.1 t2.2 chunks

@[expose] def finalChecks (n : Nat) (ta tb : ByteArray) (S : StoreOut) (chunks : Nat) : Bool :=
  let tt := Task.spawn fun _ => tree2 n ta tb S.tbi
  treeGlobal n ta tb S (stLabel n S.z0 S.z1 S.z2 chunks) tt chunks

@[expose] def stTup (keys slots tbi z0 z1 z2 : ByteArray) (q0 : Array Nat) (lev : Level) :
    Option StoreOut :=
  let ts5 := (stabMats ()).map frTable
  let tg := tupleGroup keys slots ts5 q0 stabOrder
  if !(tupleGroupOK keys nPts ts5 q0 tg.1 tg.2.1 tg.2.2.1 && tg.1.size == stabOrder) then none else
  some ⟨tbi, z0, z1, z2, q0, lev, tg.1, tg.2.2.2⟩

@[expose] def stO5 (keys slots tbi z0 z1 z2 : ByteArray) (q0 : Array Nat) : Option StoreOut :=
  let tx := (locMats ()).map frTable
  let O5 := vorbit tx (rdV2 keys stripBase) stripOrbit 23
  let o5idx := O5.pts.map fun p => findIdx keys slots p - 1
  stTup keys slots tbi z0 z1 z2 q0 ⟨NatMap.ofKeys o5idx 23, O5.par, O5.lab, #[z0, z1, z2]⟩

@[expose] def stChain (keys slots tbi z0 z1 z2 : ByteArray) (O : VOrb) (q0 : Array Nat)
    (chunks : Nat) : Option StoreOut :=
  let letters := chainLetters 15180
    (strongTables 15180 (((locMats ()).map frTable).map (posTable O)) chainWords)
  let trees := chainTrees 15180 letters chainBase
  if !(chainOK 15180 letters chainBase (Array.range qLen) chainBase trees chunks &&
      orbitSizes trees == chainSizes) then none else
  stO5 keys slots tbi z0 z1 z2 q0

@[expose] def stSig (keys slots tbi z0 z1 z2 : ByteArray) (O : VOrb) (qIdx : Array Nat)
    (chunks : Nat) : Option StoreOut :=
  let tF := frTable formRows
  let tS := frTable (sigRows (#[frApply tF rootV] ++ qIdx.map (fun i => frApply tF (rdV2 keys i))))
  if !uniqueSigOK keys nPts tS basisIdx 26 (sigTable keys tS basisIdx 26) chunks then none else
  let Mb := basisIdx.map (rdV2 keys ·)
  if !(basisIdx.size == 112 && basisIdx.all (· < nPts) && eqRows (mulRows Mb (invRows Mb)) idRows)
  then none else
  stChain keys slots tbi z0 z1 z2 O (qIdx.push stripBase) chunks

@[expose] def stO0 (keys slots tbi z0 z1 z2 : ByteArray) (chunks : Nat) : Option StoreOut :=
  let tx := (locMats ()).map frTable
  let O := vorbit tx (rdV2 keys 24) 15180 15
  if !vorbOK tx (rdV2 keys 24) O 15180 then none else
  let qIdx := (O.pts.extract 0 qLen).map fun p => findIdx keys slots p - 1
  if !(qIdx.size == qLen && (List.range qLen).all fun t =>
      decide (qIdx[t]! < nPts) && (rdV2 keys qIdx[t]!).beq O.pts[t]!) then none else
  stSig keys slots tbi z0 z1 z2 O qIdx chunks

@[expose] def stZ (keys slots tbi : ByteArray) (chunks : Nat) : Option StoreOut :=
  let txi := (locInvs ()).map frTable
  let z0 := matTab keys slots nPts txi[0]! chunks
  let z1 := matTab keys slots nPts txi[1]! chunks
  let z2 := matTab keys slots nPts txi[2]! chunks
  if !(matTabOK keys nPts txi[0]! z0 chunks && matTabOK keys nPts txi[1]! z1 chunks &&
      matTabOK keys nPts txi[2]! z2 chunks) then none else
  stO0 keys slots tbi z0 z1 z2 chunks

@[inline, expose] def andThen {α : Type} (o : Option α) (f : α → Bool) : Bool :=
  match o with
  | some a => f a
  | none => false

@[expose] def storeChecks (keys slots tb : ByteArray) (chunks : Nat) : Option StoreOut :=
  let tbi := invTab nPts tb chunks
  if !invOK32 nPts tb tbi chunks then none else stZ keys slots tbi chunks

@[expose] def j4Cert (chunks : Nat) : Bool :=
  if !matChecks then false else
  let tA := frTable rowsA
  let tB := frTable rowsB
  let bs := bfs tA tB rootV nPts
  if !(bs.count == nPts && orbitOK tA tB rootV bs nPts chunks) then false else
  let ta := bs.alpha
  let tb := bs.beta
  andThen (storeChecks bs.keys bs.slots tb chunks) fun S => finalChecks nPts ta tb S chunks

end CFSG.Sporadic.J4.Native
