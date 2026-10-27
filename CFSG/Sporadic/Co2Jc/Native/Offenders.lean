module

public import CFSG.Sporadic.Co2Jc.Words
public import CFSG.Sporadic.Co2Jc.Bits
public import CFSG.Sporadic.Co2Jc.Data.Sylow
public import CFSG.Sporadic.Co2Jc.Data.Offenders

public section

namespace CFSG.Sporadic.Co2Jc.Native

set_option compiler.extract_closed false

@[expose] def wCols (w : List Nat) : List Nat := (List.range 10).map fun i => wordAct w (2 ^ i)

@[expose] def tabF (l : List Nat) : Nat → Nat := fun i => l.getD i 0

@[expose] def compL (l₁ l₂ : List Nat) : List Nat :=
  (List.range 10).map fun i => colAct (tabF l₁) (l₂.getD i 0)

@[expose] def idTab : List Nat := (List.range 10).map fun i => 2 ^ i

@[expose] def gens : List (List Nat) :=
  (List.range 4).map fun k => wCols (Data.sylW.getD k [])

@[expose] def bfsAux (gens : List (List Nat)) : Nat → List (List Nat) → Nat → List (List Nat)
  | 0, front, _ => front
  | fuel + 1, front, i =>
    match front[i]? with
    | none => front
    | some t =>
      let front' := (List.range gens.length).foldl (fun acc k =>
        let u := compL (gens.getD k []) t
        if acc.contains u then acc else acc ++ [u]) front
      bfsAux gens fuel front' (i + 1)

@[expose] def tabs : List (List Nat) := bfsAux gens 512 [idTab] 0

@[expose] def enc (l : List Nat) : Nat := l.foldl (fun acc c => acc * 1024 + c) 0

@[expose] def tabKeys : List Nat := tabs.map enc

@[expose] def mulIdxC (s i : Nat) : Nat :=
  tabKeys.idxOf (enc (compL (tabs.getD s []) (tabs.getD i [])))

@[expose] def subs : List (List Nat) := Data.eaSubgroups

@[expose]
def fixed (l : List Nat) (m : Fin 1024) : Prop :=
  ∀ i ∈ l, colAct (tabF (tabs.getD i [])) m.val = m.val

@[expose]
def fixedB (l : List Nat) (m : Fin 1024) : Bool :=
  l.all fun i => colAct (tabF (tabs.getD i [])) m.val == m.val

@[expose] def fixCount (l : List Nat) : Nat :=
  ((Finset.univ : Finset (Fin 1024)).filter fun m => fixedB l m).card

@[expose]
def lenOK : Bool := tabs.length == 256

@[expose]
def nodupOK : Bool :=
  (List.range 256).all fun i => (List.range 256).all fun j =>
    i == j || tabs.getD i [] != tabs.getD j []

@[expose]
def tabOK : Bool := tabs.all fun l => decide (l.length = 10) && l.all (fun c => decide (c < 1024))

@[expose]
def wordsOK : Bool := Data.sylW.all fun w => w.all fun k => decide (k < 3)

@[expose]
def parentOK : Bool :=
  (tabs.getD 0 [] == idTab) &&
    (List.range tabs.length).all fun i =>
      (i == 0) || (List.range i).any fun p => (List.range 4).any fun k =>
        tabs.getD i [] == compL (gens.getD k []) (tabs.getD p [])

@[expose]
def gensOK : Bool := gens.all fun t => tabs.contains t

@[expose]
def closedOK : Bool :=
  (List.range 256).all fun i => (List.range gens.length).all fun k =>
    tabs.contains (compL (gens.getD k []) (tabs.getD i []))

@[expose]
def mulIdxOK : Bool :=
  (List.range 256).all fun s => (List.range 256).all fun i =>
    decide (mulIdxC s i < 256) &&
      tabs.getD (mulIdxC s i) [] == compL (tabs.getD s []) (tabs.getD i [])

@[expose]
def subsOK : Bool :=
  (subs.length == 715) &&
    subs.all fun l => l.contains 0 && l.all (fun i => decide (i < 256)) && decide (l.Nodup)

@[expose]
def pairOf (s : Nat) : List Nat := (List.range 256).filter fun i => i == 0 || i == s

@[expose]
def involOK : Bool :=
  (List.range 256).all fun s =>
    (s == 0) || (tabs.getD s [] == idTab) ||
      (compL (tabs.getD s []) (tabs.getD s []) != idTab) || subs.contains (pairOf s)

@[expose]
def commutesAll (s : Nat) (l : List Nat) : Bool :=
  l.all fun i =>
    compL (tabs.getD s []) (tabs.getD i []) == compL (tabs.getD i []) (tabs.getD s [])

@[expose]
def stepL (l : List Nat) (s : Nat) : List Nat :=
  let sl := l.map (mulIdxC s)
  (List.range 256).filter fun i => l.contains i || sl.contains i

@[expose]
def stepOK : Bool :=
  subs.all fun l => (List.range 256).all fun s =>
    (l.contains s) || (tabs.getD s [] == idTab) ||
      (compL (tabs.getD s []) (tabs.getD s []) != idTab) ||
      (!commutesAll s l) || subs.contains (stepL l s)

@[expose]
def boundOK : Bool := subs.all fun l => decide (l.length * fixCount l ≤ 512)

@[expose]
def checks : List Bool :=
  [lenOK, nodupOK, tabOK, wordsOK, parentOK, gensOK, closedOK, mulIdxOK, subsOK, involOK, stepOK,
    boundOK]

@[expose]
def offendersOK : Bool := checks.all id

end CFSG.Sporadic.Co2Jc.Native
