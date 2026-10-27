module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
public import CFSG.LieType.Multipliers.U42Data
public meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
public meta import CFSG.LieType.Multipliers.U42Data
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.Sporadic.SuzRecog

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native
  CFSG.Sporadic.SuzOddCore

@[expose] def matWord (w : List Nat) : Tab :=
  w.foldr (fun k t => comp 64 matTabs[k]! t) (idTab 64)

@[expose] def cWord (w : List Nat) : Array Nat :=
  w.foldr (fun k t => compA 1782 (cTab k) t) (idTab 1782)

@[expose] def treeWord (E : Enum) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, i => if i == 0 then [] else E.lab[i]! :: treeWord E fuel E.par[i]!

@[expose] def enumWord (i : Nat) : List Nat := treeWord matEnum 25920 i

@[expose] def aTab : Tab := matWord [1]

@[expose] def bTab : Tab := matWord [6, 4]

@[expose] def aInv : Tab := invTab 64 aTab

@[expose] def bInv : Tab := invTab 64 bTab

@[expose] def letterTab64 (l : Fin 2 × Bool) : Tab :=
  if l.1 = 0 then (if l.2 then aTab else aInv) else (if l.2 then bTab else bInv)

@[expose] def wordTab64 (v : List (Fin 2 × Bool)) : Tab :=
  v.foldr (fun l t => comp 64 (letterTab64 l) t) (idTab 64)

@[expose] def lBWord : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false)]

@[expose] def lBTab : Tab := wordTab64 lBWord

@[expose] def genWords : List (List (Fin 2 × Bool)) :=
  [
    [],
    [(0, true)],
    [(1, true), (0, true), (1, false)],
    [(1, true), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true),
     (1, true), (0, true), (1, true), (0, true), (1, false)],
    [(1, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true),
     (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
     (1, true), (0, true)],
    [(1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
     (1, false), (1, false), (0, true), (1, false), (0, true), (1, false), (1, false)],
    [(1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true),
     (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false),
     (0, true), (1, true), (1, true)],
    [(1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false),
     (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
     (0, true), (1, false)],
    [(1, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (1, false),
     (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false),
     (1, false), (0, true), (1, true)],
    [(1, false), (0, true), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true),
     (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, true)]
  ]

@[expose] def abCheck : Bool :=
  aInv.size == 64 && comp 64 aInv aTab == idTab 64 &&
  bInv.size == 64 && comp 64 bInv bTab == idTab 64 &&
  CFSG.LieType.Multipliers.U42.rels.all (fun r => wordTab64 r == idTab 64) &&
  wordTab64 (CFSG.LieType.Multipliers.commWords (CFSG.LieType.Multipliers.U42.coverPairs 0) ++
    [(0, false)]) == idTab 64 &&
  wordTab64 (CFSG.LieType.Multipliers.commWords (CFSG.LieType.Multipliers.U42.coverPairs 1) ++
    [(1, false)]) == idTab 64 &&
  genWords.length == 10 &&
  allBelow 10 fun k => wordTab64 (genWords.getD k []) == matTabs[k]!

@[expose] def fixInv (t : Tab) : Bool := t[1]! == 1 && comp 64 t t == idTab 64

@[expose] def invPos : List Nat := (List.range 25920).filter fun i => fixInv matEnum.tabs[i]!

@[expose] def liftTab (i : Nat) : Array Nat := cWord (enumWord i)

@[expose] def w0Tab : Array Nat := qProds[1]!

@[expose] def w0tTab : Array Nat := compA 1782 w0Tab tTab

@[expose] def commTest (x q : Array Nat) : Bool :=
  allLt 1782 fun y => x[q[w0Tab[y]!]!]! == w0Tab[x[q[y]!]!]!

@[expose] def sqTest (x q s : Array Nat) : Bool := allLt 1782 fun y => x[q[x[q[y]!]!]!]! == s[y]!

@[expose] def invTest (x q : Array Nat) : Bool := allLt 1782 fun y => x[q[x[q[y]!]!]!]! == y

@[expose] def kind (x : Array Nat) (j : Nat) : Nat :=
  if commTest x qElts[j]! then
    if sqTest x qElts[j]! w0Tab || sqTest x qElts[j]! w0tTab then 1
    else if invTest x qElts[j]! then 2 else 3
  else 0

@[expose] def conjTest (r g s : Tab) : Bool := allLt 64 fun y => r[g[y]!]! == g[s[y]!]!

@[expose] def conjOK (i : Nat) : Bool :=
  anyBelow 25920 fun c => conjTest matEnum.tabs[i]! matEnum.tabs[c]! lBTab

@[expose] def countW : Nat :=
  (invPos.map fun i => let x := liftTab i; countBelow 128 fun j => kind x j == 1).sum

@[expose] def countZ : Nat :=
  (invPos.map fun i => if conjOK i then
    (let x := liftTab i; countBelow 128 fun j => kind x j == 2) else 0).sum

@[expose] def fibreCheck : Bool :=
  invPos.all (fun i => matWord (enumWord i) == matEnum.tabs[i]! &&
    (enumWord i).all fun k => decide (k < 10)) &&
  countW == 480 && countZ == 1200

@[expose] def twistCheck : Bool := abCheck && fibreCheck

end CFSG.Sporadic.SuzRecog
