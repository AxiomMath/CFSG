module

public import CFSG.Sporadic.Recognition.McLASData
public import CFSG.Sporadic.Recognition.McLASFiveData
public import CFSG.Sporadic.SmallOddCore.McLCheckInputs
public import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Sporadic.SmallOddCore.CentData
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public import CFSG.Monster.B.Mathieu.SylowCore
public meta import CFSG.Sporadic.Recognition.McLASData
public meta import CFSG.Sporadic.Recognition.McLASFiveData
public meta import CFSG.Sporadic.SmallOddCore.McLCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Count

public section

namespace CFSG.Sporadic.Recognition.McLAS

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu

@[expose] def outerTab : Table := mclCentTbl 17

@[expose] def m11Pts : List Nat := [128, 102, 140, 182, 226, 222, 257, 71, 272, 37, 207]

@[expose] def m11Gens : Array Tab := Array.ofFn (n := 4) fun k => natArr (mclCentTbl (k.val + 18))

@[expose] def m11Rest : Array Tab := m11Gens.map (restrictArr m11Pts)

@[expose] def m11WordA : List Nat := [1]

@[expose] def m11WordB : List Nat := [3, 1, 2, 2, 2, 2, 3]

@[expose] def m11TabA : Tab := #[0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3]

@[expose] def m11TabB : Tab := #[3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10]

@[expose] def m11Check : Bool :=
  permOK 275 outerTab && (List.range 4).all (fun k => permOK 275 (mclCentTbl (k + 18))) &&
  m11Pts.length == 11 && decide m11Pts.Nodup && m11Pts.all (· < 275) &&
  (List.range 275).all (fun x => decide (x ∈ m11Pts) == ((natArr outerTab)[x]! == x)) &&
  wordTabS 11 m11Rest m11WordA == m11TabA && wordTabS 11 m11Rest m11WordB == m11TabB

@[expose] def invTab0 : Table := mclCentTbl 4

@[expose] def invProdCheck : Bool :=
  let o := conjClosureH 275 mclPGTbls mclPGInvTbls invTab0 30000
  permOK 275 invTab0 && ordTest 275 2 invTab0 &&
  allIn 0 mclPGTbls.size (fun l => invOK 275 mclPGTbls[l]! mclPGInvTbls[l]!) &&
  conjTreeOK 275 mclPGTbls mclPGInvTbls invTab0 o.1 o.2.1 o.2.2 &&
  hkeysDistinct 275 o.1.toList && o.1.size == 22275 &&
  o.1.all fun e => (List.range 6).any fun i => ordTest 275 (i + 1) (compT 275 invTab0 e)

structure ElemRow where
  rep : Table
  classSize : Nat
  centOrder : Nat
  centGens : List Table

@[expose] def elemOK (n NP cap p : Nat) (pg pgInv : Array Table) (sift : Table → Bool)
    (r : ElemRow) (o : Closure) : Bool :=
  let t := r.rep
  let cg := r.centGens.toArray
  let C := mulClosureH n cg cap
  permOK n t && sift t && ordTest n p t &&
    conjTreeOK n pg pgInv t o.1 o.2.1 o.2.2 && hkeysDistinct n o.1.toList &&
    o.1.size == r.classSize &&
    cg.all (fun c => permOK n c && sift c && commTT n c t && invOK n c (invT n c)) &&
    mulTreeOK n cg C.1 C.2.1 C.2.2 && hkeysDistinct n C.1.toList && C.1.size == r.centOrder &&
    r.classSize * r.centOrder == NP

@[expose] def elemRowsOK (n NP cap p : Nat) (pg pgInv : Array Table) (sift : Table → Bool)
    (rows : List ElemRow) : Bool :=
  allIn 0 pg.size (fun l => invOK n pg[l]! pgInv[l]!) &&
    rows.all fun r => elemOK n NP cap p pg pgInv sift r (conjClosureH n pg pgInv r.rep cap)

@[expose] def threeRow₁ : ElemRow :=
  { rep := threeTbl 0, classSize := 30800, centOrder := 29160,
    centGens := [threeTbl 0, threeTbl 1, threeTbl 2] }

@[expose] def threeRow₂ : ElemRow :=
  { rep := threeTbl 3, classSize := 924000, centOrder := 972,
    centGens := [threeTbl 3, threeTbl 4, threeTbl 5] }

@[expose] def threeRows : List ElemRow := [threeRow₁, threeRow₂]

@[expose] def threeRowsOK : Bool :=
  elemRowsOK 275 898128000 924000 3 mclPGTbls mclPGInvTbls mclSift threeRows

@[expose] def sylowThreeGens : List Table := (List.range 5).map fun i => threeTbl (i + 6)

@[expose] def sylowThreeOK : Bool :=
  let sg := sylowThreeGens.toArray
  let T := mulClosureH 275 sg 800
  permOK 275 (threeTbl 0) &&
  sg.all (fun g => permOK 275 g && mclSift g && invOK 275 g (invT 275 g)) &&
  mulTreeOK 275 sg T.1 T.2.1 T.2.2 && closedOK 275 (sg ++ sg.map (invT 275)) T.1 &&
  hkeysDistinct 275 T.1.toList && T.1.size == 729 &&
  (T.1.toList.filter fun e => sg.all (fun g => commTT 275 e g)).length == 3 &&
  memT 275 T.1 (threeTbl 0) && sg.all (fun g => commTT 275 (threeTbl 0) g)

@[expose] def fiveOuterCheck : Bool :=
  (List.range mcl275FiveC0Gens.size).any
    (fun k => !siftA 275 mcl275PLevels PairMcL.baseArr 0 mcl275FiveC0Gens[k]!) &&
  (List.range mcl275FiveC1Gens.size).any
    (fun k => !siftA 275 mcl275PLevels PairMcL.baseArr 0 mcl275FiveC1Gens[k]!)

@[expose] def fivePowerCheck : Bool :=
  validA 275 fivePowArr && siftA 275 mcl275PLevels PairMcL.baseArr 0 fivePowArr &&
    eqA 275 (conjA 275 fivePowArr mcl275FiveLines[1]!) (powArr 275 mcl275FiveLines[1]! 2)

end CFSG.Sporadic.Recognition.McLAS
