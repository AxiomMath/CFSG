module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public import Certificates.Data.FusD2Perm

public section

namespace Certificates.L34Outer

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (wordT)

structure EData where
  u : List Int
  v : List Int
  inS : Bool
  hs : List (List Int)
  ys : List (List Int)
deriving Inhabited

structure Data where
  a : List Int
  b : List Int
  z : List Int
  es : List EData
  ex : List (List Int)
deriving Inhabited

@[expose] def tGens : Array Tab := #[g₁T, g₂T, g₃T, g₄T]

@[expose] def tGensI : Array Tab := tGens.map (invTab 42)

@[expose] def rGensI : Array Tab := gTabs.map (invTab 42)

@[expose] def eT : Enum := enumBFS 42 tGens 60480

@[expose] def eS : Enum := enumBFS 42 gensS 20160

@[expose] def eR : Enum := enumBFS 42 gTabs 241920

@[expose] def checkT : Bool := invsOK 42 tGens tGensI && enumOK 42 tGens eT && eT.tabs.size == 60480

@[expose] def checkGInv : Bool := invsOK 42 gTabs rGensI

@[expose] def checkOrder3 : Bool :=
  let tIdx := indexOf eT.tabs
  allBelow eR.tabs.size fun k =>
    let r := eR.tabs[k]!
    !(comp 42 (comp 42 r r) r == idTab 42) || found tIdx eT.tabs r

@[expose] def pGens (D : Data) : Array Tab := ([D.a, D.b].map (wordT 42 tGens tGensI)).toArray

@[expose] def eP (D : Data) : Enum := enumBFS 42 (pGens D) 27

@[expose] def checkP (D : Data) : Bool := enumOK 42 (pGens D) (eP D) && (eP D).tabs.size == 27

@[expose] def eGens (e : EData) : Array Tab := ([e.u, e.v].map (wordT 42 tGens tGensI)).toArray

@[expose] def eE (e : EData) : Enum := enumBFS 42 (eGens e) 9

@[expose] def hGens (e : EData) : Array Tab := (e.hs.map (wordT 42 tGens tGensI)).toArray

@[expose] def eH (e : EData) : Enum := enumBFS 42 (hGens e) 60480

@[expose] def checkHY (eidx : Std.HashMap Tab Nat) (E : Enum) (hw yw : List Int) : Bool :=
  let h := wordT 42 tGens tGensI hw
  let hi := invTab 42 h
  let y := wordT 42 tGens tGensI yw
  let c := comp 42 (comp 42 h y) hi
  hi.size == 42 && comp 42 hi h == idTab 42 && found eidx E.tabs y && !(y == idTab 42) &&
    (c == y || c == comp 42 y y)

@[expose] def checkE (sIdx : Std.HashMap Tab Nat) (z : Tab) (e : EData) : Bool :=
  let E := eE e
  let eidx := indexOf E.tabs
  enumOK 42 (eGens e) E && E.tabs.size == 9 && found eidx E.tabs z &&
    (if e.inS then allBelow E.tabs.size (fun k => found sIdx eS.tabs E.tabs[k]!)
     else e.hs.length == e.ys.length && (e.hs.zip e.ys).all (fun p => checkHY eidx E p.1 p.2) &&
       enumOK 42 (hGens e) (eH e) && (eH e).tabs.size == 60480)

@[expose] def checkEs (D : Data) : Bool :=
  let sIdx := indexOf eS.tabs
  let z := wordT 42 tGens tGensI D.z
  !(z == idTab 42) && D.es.all (checkE sIdx z)

@[expose] def checkPairs (D : Data) : Bool :=
  let P := eP D
  let Es := D.es.map fun e => (eE e, indexOf (eE e).tabs)
  allBelow P.tabs.size fun i => allBelow P.tabs.size fun j =>
    let gs : Array Tab := #[P.tabs[i]!, P.tabs[j]!]
    let X := enumBFS 42 gs 27
    enumOK 42 gs X &&
      (X.tabs.size != 9 ||
        Es.any fun q => allBelow X.tabs.size fun k => found q.2 q.1.tabs X.tabs[k]!)

@[expose] def exGens (D : Data) : Array Tab := (D.ex.map (wordT 42 gTabs rGensI)).toArray

@[expose] def exInv (D : Data) : Array Tab := (exGens D).map (invTab 42)

@[expose] def checkExtras (D : Data) : Bool :=
  let z := wordT 42 tGens tGensI D.z
  let xs := exGens D
  let xi := exInv D
  invsOK 42 xs xi &&
    (allBelow xs.size fun j =>
      let c := comp 42 (comp 42 xs[j]! z) xi[j]!
      c == z || c == comp 42 z z) &&
    (let tIdx := indexOf eT.tabs
     allBelow eR.tabs.size fun k =>
       let r := eR.tabs[k]!
       found tIdx eT.tabs r || anyBelow xs.size fun j => found tIdx eT.tabs (comp 42 xi[j]! r))

@[expose] def check (D : Data) : Bool :=
  checkT && checkGInv && checkOrder3 && checkP D && checkEs D && checkPairs D && checkExtras D

end Certificates.L34Outer
