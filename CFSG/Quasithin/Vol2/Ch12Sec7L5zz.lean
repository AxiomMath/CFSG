module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModData2

public section

namespace CFSG.Quasithin.H13.S127.Mod

@[expose] def ex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 8
  | _ => 15

@[expose] def act4 (f : Fin 6 → Fin 6) (m : ℕ) : ℕ :=
  (if m.testBit 0 then ex (f 0) ^^^ ex (f 1) else 0) ^^^
    (if m.testBit 1 then ex (f 0) ^^^ ex (f 2) else 0) ^^^
    (if m.testBit 2 then ex (f 0) ^^^ ex (f 3) else 0) ^^^
    (if m.testBit 3 then ex (f 0) ^^^ ex (f 4) else 0)

@[expose] def permIdx (B : B6) (i : ℕ) : ℕ := oPts.idxOf (pn (B.app (oPts.getD i 0)))

@[expose] def permFn (B : B6) (i : Fin 6) : Fin 6 :=
  ⟨permIdx B i % 6, Nat.mod_lt _ (by decide)⟩

@[expose] def fVl (l : List B6) : ℕ :=
  ((List.range 64).filter fun c => l.all fun B => B.app c == c).length

@[expose] def f4l (l : List B6) : ℕ :=
  ((List.range 16).filter fun m => l.all fun B => act4 (permFn B) m == m).length

@[expose] def invs6 : List B6 := nm6.filter fun B => B.comp B == B6.id && B != B6.id

@[expose] def span2 (a b : B6) : List B6 := [B6.id, a, b, a.comp b]

@[expose] def span3 (a b c : B6) : List B6 := span2 a b ++ (span2 a b).map (·.comp c)

end CFSG.Quasithin.H13.S127.Mod
