module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModData

public section

namespace CFSG.Quasithin.H13.S127.Mod

structure B6 where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  c5 : ℕ
deriving DecidableEq

@[expose] def bitV (v i x : ℕ) : ℕ := if v.testBit i then x else 0

namespace B6

@[expose] def app (B : B6) (v : ℕ) : ℕ :=
  bitV v 0 B.c0 ^^^ bitV v 1 B.c1 ^^^ bitV v 2 B.c2 ^^^ bitV v 3 B.c3 ^^^ bitV v 4 B.c4 ^^^
    bitV v 5 B.c5

@[expose] def comp (B C : B6) : B6 :=
  ⟨B.app C.c0, B.app C.c1, B.app C.c2, B.app C.c3, B.app C.c4, B.app C.c5⟩

@[expose] def id : B6 := ⟨1, 2, 4, 8, 16, 32⟩

@[expose] def pow (B : B6) : ℕ → B6
  | 0 => id
  | n + 1 => B.comp (B.pow n)

@[expose] def Valid (B : B6) : Prop :=
  B.c0 < 64 ∧ B.c1 < 64 ∧ B.c2 < 64 ∧ B.c3 < 64 ∧ B.c4 < 64 ∧ B.c5 < 64

instance (B : B6) : Decidable B.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

end B6

@[expose] def Mc.toB6 (A : Mc) : B6 := ⟨A.c0, wV A.c0, A.c1, wV A.c1, A.c2, wV A.c2⟩

@[expose] def sig6 : B6 := ⟨1, 3, 4, 12, 16, 48⟩

@[expose] def gm6 : List B6 := gmList.map Mc.toB6

@[expose] def nm6 : List B6 := gm6 ++ gm6.map (·.comp sig6)

@[expose] def inv6 (B : B6) : B6 := B.pow 59

@[expose] def two6 (B : B6) : Bool := B.pow 4 == B6.id

@[expose] def ord3 (B : B6) : Bool := B.pow 3 == B6.id && B != B6.id

@[expose] def fixCount (B : B6) : ℕ := ((List.range 64).filter fun c => B.app c == c).length

@[expose] def oVecL : List ℕ := (List.range 64).filter fun c => c != 0 && oPts.contains (pn c)

@[expose] def zsm : List Mc := [⟨1, 4, 16⟩, ⟨2, 8, 32⟩, ⟨3, 12, 48⟩]

@[expose] def zs6 : List B6 := zsm.map Mc.toB6

@[expose] def w6 : B6 := Mc.toB6 ⟨2, 8, 32⟩

@[expose] def p1c : List ℕ := [0, 5, 10, 15]

@[expose] def l2c : List ℕ := List.range 16

@[expose] def presv (l : List ℕ) (B : B6) : Bool := l.all fun c => l.contains (B.app c)

@[expose] def s0m : List Mc :=
  [⟨1, 4, 16⟩, ⟨1, 4, 21⟩, ⟨1, 4, 27⟩, ⟨1, 4, 30⟩, ⟨4, 1, 16⟩, ⟨4, 1, 21⟩, ⟨4, 1, 27⟩, ⟨4, 1, 30⟩]

@[expose] def s0 : List B6 := s0m.map Mc.toB6

@[expose] def s0p : List B6 := s0 ++ s0.map (·.comp sig6)

@[expose] def r1m : List Mc := [⟨1, 4, 16⟩, ⟨1, 4, 21⟩, ⟨4, 1, 16⟩, ⟨4, 1, 21⟩]

@[expose] def r2m : List Mc := [⟨1, 4, 16⟩, ⟨1, 4, 21⟩, ⟨1, 4, 27⟩, ⟨1, 4, 30⟩]

@[expose] def r1 : List B6 := r1m.map Mc.toB6

@[expose] def r2 : List B6 := r2m.map Mc.toB6

@[expose] def l1m : List Mc :=
  [⟨1, 4, 16⟩, ⟨1, 4, 21⟩, ⟨4, 1, 16⟩, ⟨4, 1, 21⟩, ⟨16, 21, 27⟩, ⟨16, 21, 30⟩, ⟨21, 16, 27⟩,
    ⟨21, 16, 30⟩, ⟨27, 30, 1⟩, ⟨27, 30, 4⟩, ⟨30, 27, 1⟩, ⟨30, 27, 4⟩]

@[expose] def l2m : List Mc :=
  [⟨1, 4, 16⟩, ⟨1, 4, 21⟩, ⟨1, 4, 27⟩, ⟨1, 4, 30⟩, ⟨2, 12, 16⟩, ⟨2, 12, 21⟩, ⟨2, 12, 27⟩,
    ⟨2, 12, 30⟩, ⟨3, 8, 16⟩, ⟨3, 8, 21⟩, ⟨3, 8, 27⟩, ⟨3, 8, 30⟩]

@[expose] def l1 : List B6 := l1m.map Mc.toB6

@[expose] def l2 : List B6 := l2m.map Mc.toB6

@[expose] def onQuot (B : B6) : Bool :=
  presv l2c B && (List.range 64).all fun c => l2c.contains (c ^^^ B.app c)

@[expose] def fixP1 (B : B6) : Bool := p1c.all fun c => B.app c == c

@[expose] def i1 : B6 := ⟨4, 12, 1, 3, 21, 63⟩

@[expose] def i2 : B6 := ⟨4, 12, 1, 3, 16, 48⟩

@[expose] def spanX (l : List ℕ) : List ℕ :=
  l.foldl (fun acc g => if acc.contains g then acc else acc ++ acc.map (· ^^^ g)) [0]

@[expose] def dreps : List Mc :=
  [⟨1, 4, 16⟩, ⟨1, 8, 48⟩, ⟨1, 12, 32⟩, ⟨1, 16, 4⟩, ⟨1, 32, 12⟩, ⟨1, 48, 8⟩, ⟨2, 8, 32⟩,
    ⟨2, 12, 16⟩, ⟨2, 16, 12⟩, ⟨2, 32, 8⟩, ⟨2, 48, 4⟩, ⟨3, 12, 48⟩, ⟨3, 16, 8⟩, ⟨3, 32, 4⟩,
    ⟨3, 48, 12⟩, ⟨16, 21, 1⟩, ⟨16, 27, 3⟩, ⟨16, 39, 1⟩, ⟨16, 42, 3⟩, ⟨16, 54, 1⟩, ⟨16, 63, 2⟩,
    ⟨32, 39, 3⟩, ⟨32, 42, 2⟩, ⟨32, 54, 3⟩, ⟨32, 63, 1⟩, ⟨48, 54, 2⟩, ⟨48, 63, 3⟩]

@[expose] def closureM (gens : List Mc) : List Mc :=
  bfs gens 64 ((Array.replicate 262144 false).set! (mcIdx Mc.one) true, [Mc.one], [Mc.one])

@[expose] def spanHas (l ds : List ℕ) : Bool :=
  let s := spanX l
  ds.all fun d => s.contains d

@[expose] def genAll (gens : List Mc) : Bool :=
  let cl := closureM gens
  gmList.all fun g => cl.contains g

@[expose] def ct3 : List Mc := [⟨1, 12, 39⟩, ⟨1, 63, 32⟩]

end CFSG.Quasithin.H13.S127.Mod

end
