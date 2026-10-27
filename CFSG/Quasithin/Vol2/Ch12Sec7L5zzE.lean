module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import Mathlib.Data.List.Defs
public import Mathlib.Tactic.Finiteness.Attr

public section

namespace CFSG.Quasithin.H13.S127.Mod

@[expose] def stabC1 (c : ℕ) : List B6 := nm6.filter fun B => B.app c == c && B.app 1 == 1

@[expose] def cpat (b : ℕ) (d : Fin 7) : Bool :=
  match d.val with
  | 0 => true
  | 1 => b.testBit 0
  | 6 => b.testBit 0
  | 2 => b.testBit 1
  | 5 => b.testBit 1
  | _ => b.testBit 2

@[expose] def ext7 (f : Fin 6 → Fin 6) (k : Fin 7) : Fin 7 :=
  if h : k.val = 0 then 0 else (f ⟨k.val - 1, by omega⟩).succ

@[expose] def fl (l : List (Fin 6)) (i : Fin 6) : Fin 6 := l.getD i 0

@[expose] def perms6 : List (List (Fin 6)) := (List.finRange 6).permutations

@[expose] def cycOK (b : ℕ) (f : Fin 6 → Fin 6) : Bool :=
  (List.finRange 7).all fun i => (List.finRange 7).all fun j =>
    cpat b (ext7 f j - ext7 f i) == cpat b (j - i)

@[expose] def cycMoved (b : ℕ) (f : Fin 6 → Fin 6) : Bool :=
  (List.finRange 7).all fun k => ext7 f k == k || cpat b (ext7 f k - k)

end CFSG.Quasithin.H13.S127.Mod
