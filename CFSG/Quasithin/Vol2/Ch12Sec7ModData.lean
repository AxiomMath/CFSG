module

public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.Quasithin.H13.S127.Mod

@[expose] def wV (v : ℕ) : ℕ :=
  ((v >>> 1) &&& 21) ||| (((v &&& 21) ^^^ ((v >>> 1) &&& 21)) <<< 1)

@[expose] def sV (c v : ℕ) : ℕ :=
  (if c % 2 = 1 then v else 0) ^^^ (if (c >>> 1) % 2 = 1 then wV v else 0)

structure Mc where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
deriving DecidableEq

namespace Mc

@[expose] def Valid (A : Mc) : Prop := A.c0 < 64 ∧ A.c1 < 64 ∧ A.c2 < 64

instance (A : Mc) : Decidable A.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

@[expose] def app (A : Mc) (v : ℕ) : ℕ :=
  sV (v &&& 3) A.c0 ^^^ sV ((v >>> 2) &&& 3) A.c1 ^^^ sV ((v >>> 4) &&& 3) A.c2

@[expose] def mul (A B : Mc) : Mc := ⟨A.app B.c0, A.app B.c1, A.app B.c2⟩

@[expose] def one : Mc := ⟨1, 4, 16⟩

@[expose] def pow (A : Mc) : ℕ → Mc
  | 0 => one
  | n + 1 => A.mul (A.pow n)


end Mc

@[expose] def invC (c : ℕ) : ℕ := if c = 2 then 3 else if c = 3 then 2 else c

@[expose] def pn (v : ℕ) : ℕ :=
  if v &&& 3 ≠ 0 then sV (invC (v &&& 3)) v
  else if (v >>> 2) &&& 3 ≠ 0 then sV (invC ((v >>> 2) &&& 3)) v
  else sV (invC ((v >>> 4) &&& 3)) v

@[expose] def oPts : List ℕ := [1, 4, 16, 21, 57, 45]

@[expose] def inGm (A : Mc) : Bool :=
  (oPts.all fun p => oPts.contains (pn (A.app p))) && decide (oPts.map fun p => pn (A.app p)).Nodup

@[expose] def gmGens : List Mc := [⟨8, 16, 63⟩, ⟨1, 12, 39⟩]

@[expose] def mcIdx (A : Mc) : ℕ := A.c0 + 64 * A.c1 + 4096 * A.c2

@[expose] def bfsAdd (gens : List Mc) (sn : Array Bool × List Mc) (x : Mc) : Array Bool × List Mc :=
  gens.foldl (fun sn g =>
    if sn.1.getD (mcIdx (x.mul g)) false then sn
    else (sn.1.set! (mcIdx (x.mul g)) true, x.mul g :: sn.2)) sn

@[expose] def bfsStep (gens : List Mc) (st : Array Bool × List Mc × List Mc) :
    Array Bool × List Mc × List Mc :=
  let sn := st.2.2.foldl (bfsAdd gens) (st.1, [])
  (sn.1, st.2.1 ++ sn.2, sn.2)

@[expose] def bfs (gens : List Mc) : ℕ → Array Bool × List Mc × List Mc → List Mc
  | 0, st => st.2.1
  | n + 1, st => if st.2.2 = [] then st.2.1 else bfs gens n (bfsStep gens st)

@[expose] def gmList : List Mc :=
  bfs gmGens 64 ((Array.replicate 262144 false).set! (mcIdx Mc.one) true, [Mc.one], [Mc.one])

end CFSG.Quasithin.H13.S127.Mod

end
