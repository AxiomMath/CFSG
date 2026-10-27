module

public import Certificates.Data.SolMaxSixGen
public import Mathlib.GroupTheory.Perm.Support

public section

namespace CFSG.ComponentClassification.SolMax.SixGen

open CFSG.PSL3Four.Native

@[expose] def evW (gs : List (Equiv.Perm (Fin 9))) (w : List ℕ) : Equiv.Perm (Fin 9) :=
  (w.map fun i => gs.getD i 1).prod

@[expose] def entryCommK (e : Swaps × List Swaps) : Bool :=
  let u := tabOf (permOf u₀)
  let v := tabOf (permOf e.1)
  let uv := comp 9 u v
  (e.2.map fun l => tabOf (permOf l)).all fun g => commutes g u || commutes g v || commutes g uv

@[expose] def evenSwapsK (l : Swaps) : Bool := l.length % 2 == 0 && l.all fun p => p.1 != p.2

@[expose] def reachK (gs : List (Equiv.Perm (Fin 9))) (T S : List (List ℕ)) (C : List ℕ) : Bool :=
  (List.finRange 9).all (fun q => decide (evW gs (T.getD q.val []) 0 = q)) &&
    (List.finRange 9).all (fun q => q == 0 ||
      (decide (evW gs (S.getD q.val []) 0 = 0) && decide (evW gs (S.getD q.val []) 1 = q))) &&
    decide ((evW gs C).support.card = 3)

@[expose] def entryWitK (e : Swaps × List Swaps) (T S : List (List ℕ)) (C : List ℕ) : Bool :=
  entryCommK e && e.2.all evenSwapsK && reachK (e.2.map permOf) T S C

@[expose] def cgTabs : Array Tab := (centGens.map fun l => tabOf (permOf l)).toArray

@[expose] def cgCommK : Bool := centGens.all fun l => commutes (tabOf (permOf l)) (tabOf (permOf u₀))

@[expose] def coverK (E : Enum) : Bool :=
  let vs := entries.map fun e => tabOf (permOf e.1)
  E.tabs.toList.all fun w => !(comp 9 w w == idTab 9) || vs.contains w

@[expose] def sixGenWitK (T S : List (List (List ℕ))) (C : List (List ℕ)) : Bool :=
  (List.range entries.length).all fun i =>
    entryWitK (entries.getD i default) (T.getD i []) (S.getD i []) (C.getD i [])

end CFSG.ComponentClassification.SolMax.SixGen

end
