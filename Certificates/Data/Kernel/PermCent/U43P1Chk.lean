module

public import Certificates.Data.Kernel.PermCent.U43P1
public import Certificates.Data.Kernel.ConjOrb

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43.Cover

open CFSG.KC.Enum CFSG.KS CFSG.KC.ConjOrb

@[expose] noncomputable def at10 (p i : ℕ) : ℕ := pg 10 (mask 10) p i

@[expose] noncomputable def pc (p q : ℕ) : ℕ := pcomp 820 10 (mask 10) p q

@[expose] noncomputable def pk (k : ℕ) (ε : Bool) : ℕ := pmk 820 10 (imgK k ε)

@[expose] noncomputable def isId (p : ℕ) : Bool := (List.range 820).all fun i => Nat.beq (at10 p i) i

@[expose] noncomputable def invol (p : ℕ) : Bool := isId (pc p p) && !isId p

@[expose] noncomputable def matOK (k : ℕ) (ε : Bool) (p : ℕ) : Bool :=
  (List.range 820).all fun i => Nat.beq (at10 p i) (imgK k ε i)

@[expose] noncomputable def gensOK (l : List (ℕ × Bool)) (G : ℕ → ℕ) : Bool :=
  (List.range l.length).all fun j => matOK (l.getD j (0, false)).1 (l.getD j (0, false)).2 (G j)

@[expose] noncomputable def dgOK (k : ℕ) (y : List ℕ) (p : ℕ) : Bool :=
  (List.range 826).all fun i => Nat.beq (pg 10 (mask 10) p i)
    (cond (Nat.blt i 820) (imgK k false i) (y.getD (i - 820) 0 + 820))

@[expose] noncomputable def y6OK (y : List ℕ) (p : ℕ) : Bool :=
  (List.range 6).all fun i => Nat.beq (pg 3 (mask 3) p i) (y.getD i 0)

@[expose] noncomputable def tabOK (a : Array ℕ) (p : ℕ) : Bool :=
  (List.range 820).all fun i => Nat.beq (at10 p i) a[i]!

@[expose] noncomputable def commOK (p q : ℕ) : Bool := Nat.beq (pc p q) (pc q p)

@[expose] noncomputable def notOrd8F (x4 : ℕ) : Bool := isId x4 || !isId (pc x4 x4)

@[expose] noncomputable def notOrd8 (x : ℕ) : Bool := notOrd8F ((fun x2 => pc x2 x2) (pc x x))

@[expose] noncomputable def inCls (cls : ℕ → ℕ → ℕ) (sz : ℕ → ℕ) (cs : List ℕ) (c j x : ℕ) :
    Bool :=
  cs.contains c && Nat.blt j (sz c) && Nat.beq (cls c j) x

@[expose] noncomputable def coverOK (S : ℕ → ℕ) (cls : ℕ → ℕ → ℕ) (sz : ℕ → ℕ) (cs : List ℕ)
    (W : List ℕ) : Bool :=
  (W.zipIdx).all fun x =>
    cond (Nat.beq x.1 0) (!invol (S x.2))
      (inCls cls sz cs ((x.1 - 1) / 65536) ((x.1 - 1) % 65536) (S x.2))

@[expose] noncomputable def lookOK (u : ℕ) (cls : ℕ → ℕ → ℕ) (sz : ℕ → ℕ) (cs : List ℕ)
    (rs : List (ℕ × ℕ)) (W : List ℕ) : Bool :=
  Nat.beq rs.length W.length && (rs.zip W).all fun x =>
    inCls cls sz cs (x.2 / 65536) (x.2 % 65536) (pc u (pc (cls x.1.1 x.1.2) u))

@[expose] noncomputable def cfgOK (T : ℕ → ℕ) (cls : ℕ → ℕ → ℕ) (sz : ℕ → ℕ) (inner : Bool)
    (mem : ℕ → Bool) (Ls : List ℕ) (d dI : ℕ) (W : List ℕ) : Bool :=
  (W.zipIdx).all fun x =>
    cond (Nat.beq x.1 0) (!invol (T x.2))
      (cond (Nat.beq x.1 1) (inner && mem (T x.2))
        (cond (Nat.beq x.1 2) (Ls.all fun l => notOrd8 (pc (T x.2) l))
          (cond (Nat.blt ((x.1 - 3) / 65536) 2)
            (inCls cls sz [0, 1] ((x.1 - 3) / 65536) ((x.1 - 3) % 65536) (T x.2))
            (inCls cls sz [0, 1] ((x.1 - 3) / 65536 - 2) ((x.1 - 3) % 65536)
              (pc dI (pc (T x.2) d))))))

end CFSG.ComponentClassification.HarrisLit.P1.U43.Cover
