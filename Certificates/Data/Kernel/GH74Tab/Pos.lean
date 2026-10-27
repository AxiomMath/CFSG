module

public import Certificates.Data.Kernel.GH74Tab.Defs

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def posP {n : ℕ} [NeZero n] (t : Tab n) (a : Tbl) (_ : Fin 64) : Bool :=
  (List.finRange 64).all fun i => imp (t.isQ.get i) (decide ((t.el.get (a.get i)).2 = 1))

@[expose] def s2OK (n : ℕ) [NeZero n] (S2 : Nat) : Bool :=
  (List.finRange 64).all fun k => decide (((mkTab n).el.get k).2 = 1) == bit S2 k

@[expose] def posOK (D : Dat) (S2 : Nat) (L : List (Nat × Nat)) : Bool :=
  L.all fun p => r64.all fun i => !bit D.Q i || bit S2 (g6 p.1 i)

end CFSG.KC.GH74Tab

end
