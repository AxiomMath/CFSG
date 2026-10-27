module

public import CFSG.Sporadic.SuzRecog.LocalRFusionTests
public import Certificates.Data.SuzLevelTwoBase
public import Certificates.Data.C1ModelData
public import Certificates.Data.CFSGNative.PSL3Four.L34Aut

public section

namespace CFSG.Sporadic.SuzRecog.C1Model

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1ModelData

@[expose] def w0T : Tab := LevelTwoData.w0Arr

@[expose] def rhoT : Tab := LevelTwoData.rhoArr

@[expose] def rhoI : Tab := invTab 1782 rhoT

@[expose] def r1T : Tab := conjTab 1782 rhoT rhoI w0T

@[expose] def r2T : Tab := conjTab 1782 rhoT rhoI r1T

@[expose] def l4T : Tab := cWord LocalR.lambda4Word

@[expose] def gcT : Tab := cWord [6, 9, 2]

@[expose] def gcI : Tab := invTab 1782 gcT

@[expose] def rhoDecT : Tab := comp 1782 (comp 1782 (cWord [6, 8, 7, 4, 7, 4]) qProds[30]!) tTab

@[expose] def tauT : Tab := comp 1782 (cWord [5, 8, 6, 7, 4]) qProds[23]!

@[expose] def decTab (d : List Nat × Nat) : Tab := comp 1782 (cWord d.1) qElts[d.2]!

@[expose] def bgT : Tab := comp 1782 b0Arr b1Arr

@[expose] def bgI : Tab := invTab 1782 bgT

@[expose] def bwT : Tab := conjTab 1782 gcT gcI bgT

@[expose] def bwI : Tab := invTab 1782 bwT

@[expose] def cwT : Tab := comp 1782 (comp 1782 (comp 1782 w0T bwT) w0T) bwI

@[expose] def zT : Tab := powTab 1782 (comp 1782 bwI (powTab 1782 cwT 7)) 2

@[expose] def hT : Tab :=
  comp 1782 (powTab 1782 (comp 1782 w0T (conjTab 1782 bgT bgI b0Arr)) 8) bgT

@[expose] def wordTab (n : Nat) (gens : Array Tab) (w : List Nat) : Tab :=
  w.foldr (fun k t => comp n gens[k]! t) (idTab n)

@[expose] def t0Tab (i : Nat) : Tab := decTab (t0Decs.getD i ([], 0))

@[expose] def t0Tabs : Array Tab := Array.ofFn (n := 4) fun i => t0Tab i.val

@[expose] def v0Tab (j : Nat) : Tab :=
  if j < 4 then t0Tab j else if j = 4 then w0T else if j = 5 then r1T else tauT

@[expose] def v0Tabs : Array Tab := Array.ofFn (n := 7) fun j => v0Tab j.val

@[expose] def b0Tab (j : Nat) : Tab :=
  if j < 4 then t0Tab j else if j = 4 then w0T else if j = 5 then rhoT else tauT

@[expose] def b0Tabs : Array Tab := Array.ofFn (n := 7) fun j => b0Tab j.val

@[expose] def nt0Tab (j : Nat) : Tab :=
  if j < 7 then v0Tab j else decTab (nt0Decs.getD (j - 7) ([], 0))

@[expose] def nt0Tabs : Array Tab := Array.ofFn (n := 11) fun j => nt0Tab j.val

@[expose] def ce3Tab (i : Nat) : Tab := decTab (ce3Decs.getD i ([], 0))

@[expose] def ce3Tabs : Array Tab := Array.ofFn (n := 2) fun i => ce3Tab i.val

@[expose] def kTab (i : Nat) : Tab := cWord (kWords.getD i [])

@[expose] def kTabs : Array Tab := Array.ofFn (n := 8) fun i => kTab i.val

@[expose] def e3xT : Tab := cWord e3Word

@[expose] def e3xI : Tab := invTab 1782 e3xT

@[expose] def e3T : Tab := conjTab 1782 e3xT e3xI (cWord [1])

@[expose] def t0ConjTab (i : Nat) : Tab := wordTab 1782 #[tTab, zT] (t0ConjWords.getD i [])

@[expose] def t0Enum : Enum := enumBFS 1782 t0Tabs 64

@[expose] def v0Enum : Enum := enumBFS 1782 v0Tabs 512

@[expose] def ct0Tab (i : Nat) : Tab := wordTab 1782 ce3Tabs (ct0Words.getD i [])

@[expose] def ct0Gens : Array Tab := Array.ofFn (n := 3) fun i => ct0Tab i.val

@[expose] def ct0Enum : Enum := enumBFS 1782 ct0Gens 192

@[expose] def cosTab (a : Nat) : Tab := wordTab 1782 ce3Tabs (cosWords.getD a [])

@[expose] def cosTabs : Array Tab := Array.ofFn (n := 48) fun a => cosTab a.val

@[expose] def cosInvs : Array Tab := cosTabs.map (invTab 1782)

@[expose] def cosKey (a i : Nat) : Tab := conjTab 1782 cosTabs[a]! cosInvs[a]! t0Tabs[i]!

@[expose] def a4Enum : Enum := enumBFS 1782 #[w0T, rhoT] 12

@[expose] def commT0 (x : Tab) : Bool :=
  allBelow 4 fun i => comp 1782 x t0Tabs[i]! == comp 1782 t0Tabs[i]! x

@[expose] def ct0Tabs : Array Tab := ct0Enum.tabs

@[expose] def c0Tabs : Array Tab := v0Enum.tabs.filter commT0

@[expose] def c0Invs : Array Tab := c0Tabs.map (invTab 1782)

@[expose] def tcTabs : Array Tab :=
  Array.ofFn (n := 1024) fun m => comp 1782 t0Enum.tabs[m.val / 16]! c0Tabs[m.val % 16]!

@[expose] def t0Invols : Array Tab := t0Enum.tabs.filter fun e => comp 1782 e e == idTab 1782

@[expose] def isJ (x : Tab) : Bool :=
  comp 1782 x r1T == comp 1782 r1T x && comp 1782 x rhoT == comp 1782 rhoT x

@[expose] def conjEq (a u y : Tab) : Bool :=
  (allBelow 4 fun i => a[u[i]!]! == y[a[i]!]!) && comp 1782 a u == comp 1782 y a

@[expose] def a4Tabs : Array Tab := ct0Tabs.filter fun x => comp 1782 x zT == comp 1782 zT x

@[expose] def isY (x : Tab) : Bool :=
  comp 1782 x x == idTab 1782 && !(x == idTab 1782) && fixedCount x == 42

@[expose] def yTabs : Array Tab := ct0Tabs.filter isY

@[expose] def b0Invs : Array Tab := b0Tabs.map (invTab 1782)

@[expose] def b0Orbit : Enum := orbitBFS 1782 b0Tabs b0Invs w0T 3

@[expose] def nt0Invs : Array Tab := nt0Tabs.map (invTab 1782)

@[expose] def nt0Orbit : Enum := orbitBFS 1782 nt0Tabs nt0Invs w0T 24

@[expose] def labArr : Array Nat := labList.toArray

@[expose] def labInv : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate 1782 0
  for i in [0:42] do
    r := r.set! labArr[i]! i
  return r

@[expose] def resTab (t : Tab) : Tab := Array.ofFn (n := 42) fun i => labInv[t[labArr[i]!]!]!

@[expose] def baseCheck : Bool :=
  permOK 1782 w0T && permOK 1782 rhoT &&
    gcI.size == 1782 && comp 1782 gcI gcT == idTab 1782 &&
    w0T == comp 1782 (comp 1782 gcT l4T) gcI && rhoT == rhoDecT &&
    rhoI.size == 1782 && comp 1782 rhoI rhoT == idTab 1782 &&
    comp 1782 w0T w0T == idTab 1782 && !(w0T == idTab 1782) &&
    comp 1782 w0T r1T == comp 1782 r1T w0T && !(r1T == w0T) && r2T == comp 1782 w0T r1T &&
    comp 1782 tauT tauT == idTab 1782 && comp 1782 tauT w0T == comp 1782 w0T tauT &&
    comp 1782 tauT r1T == comp 1782 r2T tauT && comp 1782 tauT rhoT == comp 1782 rhoI tauT &&
    bgI.size == 1782 && comp 1782 bgI bgT == idTab 1782 &&
    bwI.size == 1782 && comp 1782 bwI bwT == idTab 1782 &&
    comp 1782 zT w0T == comp 1782 w0T zT && comp 1782 zT r1T == comp 1782 r1T zT &&
    comp 1782 zT rhoT == comp 1782 rhoT zT &&
    comp 1782 hT (tArr 0) == comp 1782 w0T hT

@[expose] def resCheck : Bool :=
  labArr.size == 42 &&
    (allBelow 42 fun i => decide (labArr[i]! < 1782) && w0T[labArr[i]!]! == labArr[i]! &&
      labInv[labArr[i]!]! == i) &&
    (allBelow 1782 fun x => !(w0T[x]! == x) || (decide (labInv[x]! < 42) && labArr[labInv[x]!]! == x)) &&
    resTab tTab == wordTab 42 gensS resT1Word && resTab zT == wordTab 42 gensS resZWord &&
    (allBelow 3 fun k => gensS[k]! == wordTab 42 #[resTab tTab, resTab zT] (gensSWords.getD k [])) &&
    resTab tauT == comp 42 (wordTab 42 gensS tauSWord) r₄T

@[expose] def t0Check : Bool :=
  enumOK 1782 t0Tabs t0Enum && t0Enum.tabs.size == 64 &&
    (allBelow 4 fun i => comp 1782 t0Tabs[i]! w0T == comp 1782 w0T t0Tabs[i]! &&
      comp 1782 t0Tabs[i]! r1T == comp 1782 r1T t0Tabs[i]! &&
      comp 1782 t0Tabs[i]! rhoT == comp 1782 rhoT t0Tabs[i]!) &&
    (allBelow 4 fun i => comp 1782 (t0ConjTab i) tTab == comp 1782 t0Tabs[i]! (t0ConjTab i)) &&
    e3xI.size == 1782 && comp 1782 e3xI e3xT == idTab 1782 &&
    found (indexOf t0Enum.tabs) t0Enum.tabs e3T

@[expose] def v0Check : Bool :=
  let idx := indexOf t0Enum.tabs
  enumOK 1782 v0Tabs v0Enum && v0Enum.tabs.size == 512 &&
    allBelow 512 fun k =>
      !(comp 1782 v0Enum.tabs[k]! v0Enum.tabs[k]! == idTab 1782) ||
        v0Enum.tabs[k]! == idTab 1782 || fixedCount v0Enum.tabs[k]! == 42 ||
        found idx t0Enum.tabs v0Enum.tabs[k]!

@[expose] def centCheck : Bool :=
  (allBelow 2 fun i => comp 1782 ce3Tabs[i]! e3T == comp 1782 e3T ce3Tabs[i]!) &&
    enumOK 1782 ct0Gens ct0Enum && ct0Enum.tabs.size == 192 &&
    (allBelow 3 fun i => commT0 ct0Gens[i]!) && invsOK 1782 cosTabs cosInvs &&
    (allBelow 48 fun a => allBelow a fun b => !(allBelow 4 fun i => cosKey a i == cosKey b i)) &&
    a4Tabs.size == 12 && yTabs.size == 24 &&
    c0Tabs.size == 16 && (allBelow 16 fun i => comp 1782 c0Tabs[i]! r1T == comp 1782 r1T c0Tabs[i]!) &&
    enumOK 1782 #[w0T, rhoT] a4Enum && a4Enum.tabs.size == 12

@[expose] def locCheck : Bool :=
  let idx := indexOf tcTabs
  (allBelow 16 fun i => (c0Invs[i]!).size == 1782 && comp 1782 c0Invs[i]! c0Tabs[i]! == idTab 1782) &&
    allBelow 512 fun k =>
      let x := v0Enum.tabs[k]!
      found idx tcTabs x ||
        (let xi := invTab 1782 x
         xi.size == 1782 && comp 1782 xi x == idTab 1782 &&
          (anyBelow 16 fun i =>
            !isJ (comp 1782 (comp 1782 (comp 1782 x c0Tabs[i]!) xi) c0Invs[i]!)) &&
          anyBelow t0Invols.size fun j =>
            let e := t0Invols[j]!
            let y := conjTab 1782 x xi e
            !(comp 1782 e y == comp 1782 y e))

@[expose] def rhoTail (c : Tab) : Bool :=
  let c2 := comp 1782 c c
  comp 1782 c2 w0T == comp 1782 w0T c2 ||
    (let c3 := comp 1782 c c2
     comp 1782 c3 w0T == comp 1782 w0T c3 && (!(c3 == idTab 1782) || commT0 c))

@[expose] def rhoCand (c u l : Tab) : Bool :=
  !(conjEq c u w0T || conjEq c u u || conjEq c u l) || rhoTail c

@[expose] def rhoCond (idx : Std.HashMap Tab Nat) (u : Tab) : Bool :=
  comp 1782 u u == idTab 1782 && !(u == idTab 1782) && !(u == w0T) &&
    !found idx t0Enum.tabs u && !found idx t0Enum.tabs (comp 1782 w0T u)

@[expose] def rhoCheck : Bool :=
  let idx := indexOf t0Enum.tabs
  allBelow 16 fun i =>
    !rhoCond idx c0Tabs[i]! ||
      let l := comp 1782 w0T c0Tabs[i]!
      allBelow 2 fun s =>
        anyBelow 8 fun j =>
          comp 1782 kTabs[j]! w0T == comp 1782 (if s = 0 then c0Tabs[i]! else l) kTabs[j]! &&
            allBelow 512 fun m => rhoCand (comp 1782 kTabs[j]! v0Enum.tabs[m]!) c0Tabs[i]! l

@[expose] def normCheck : Bool :=
  orbitOK 1782 b0Tabs b0Invs w0T b0Orbit && b0Orbit.tabs.size == 3 &&
    normalOK 1782 t0Enum.tabs nt0Tabs nt0Invs t0Tabs &&
    orbitOK 1782 nt0Tabs nt0Invs w0T nt0Orbit && nt0Orbit.tabs.size == 24

end CFSG.Sporadic.SuzRecog.C1Model
