module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public meta import Certificates.Data.CFSGNative.PSL3Four.L34Aut

public section

namespace Certificates.L34TwoSig

open CFSG.PSL3Four.Native

@[expose] def b1T : Tab :=
  #[2, 0, 1, 3, 4, 9, 6, 19, 16, 10, 5, 20, 15, 11, 8, 17, 14, 12, 7, 18, 13, 30, 31, 21, 32, 33,
    26, 22, 38, 34, 23, 27, 37, 40, 41, 35, 28, 24, 36, 39, 25, 29]

@[expose] def b2T : Tab :=
  #[15, 12, 17, 6, 3, 9, 4, 18, 8, 10, 5, 2, 20, 0, 14, 13, 16, 11, 19, 7, 1, 30, 32, 21, 33, 31,
    35, 24, 28, 41, 23, 37, 40, 27, 29, 39, 36, 25, 38, 26, 22, 34]

@[expose] def bGens : Array Tab := #[b1T, b2T]

@[expose] def bEnum (_ : Unit := ()) : Enum := enumBFS 42 bGens 9

@[expose] def sqIter : Nat → Tab → Tab
  | 0, t => t
  | k + 1, t => sqIter k (comp 42 t t)

@[expose] def is2 (t : Tab) : Bool := sqIter 8 t == idTab 42

@[expose] def conjAt (BE BI : Array Tab) (r : Tab) (i : Nat) : Tab := conjTab 42 BE[i]! BI[i]! r

@[expose] def cStep (BE BI : Array Tab) (r : Tab) (j : Nat) (t : Tab) : Tab :=
  comp 42 (conjAt BE BI r j) t

@[expose] def cSearch (BE BI : Array Tab) (r : Tab) : Enum :=
  bfs (cStep BE BI r) BE.size (idTab 42) 200

@[expose] def pathOK (step : Nat → Tab → Tab) (k : Nat) (E : Enum) : Bool :=
  0 < E.tabs.size && E.tabs[0]! == idTab 42 &&
    allBelow E.tabs.size fun i =>
      i == 0 || (E.par[i]! < i && E.lab[i]! < k && E.tabs[i]! == step E.lab[i]! E.tabs[E.par[i]!]!)

@[expose] def elemOK (BE BI : Array Tab) (r : Tab) : Bool :=
  !is2 r || (comp 42 b1T r == comp 42 r b1T && comp 42 b2T r == comp 42 r b2T) ||
    (anyBelow BE.size fun i => anyBelow BE.size fun j =>
      !is2 (comp 42 (conjAt BE BI r i) (conjAt BE BI r j))) ||
    (let E := cSearch BE BI r
     pathOK (cStep BE BI r) BE.size E && anyBelow E.tabs.size fun i => !is2 E.tabs[i]!)

@[expose] def l34TwoSigCheck (ES ER : Array Tab) : Bool :=
  let idxS := indexOf ES
  let E := bEnum ()
  let BI := E.tabs.map (invTab 42)
  found idxS ES b1T && found idxS ES b2T && enumOK 42 bGens E && E.tabs.size == 9 &&
    invsOK 42 E.tabs BI && allBelow ER.size fun k => elemOK E.tabs BI ER[k]!

end Certificates.L34TwoSig
