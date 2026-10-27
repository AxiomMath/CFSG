module

public import Certificates.Data.Kernel.HMathieu.Bfs
public import Certificates.Data.Kernel.HMathieu.Greedy
public import CFSG.Quasithin.Background.HMathieuBits

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def invFrom (e0 : Nat) : List Nat → Nat → List Nat
  | [], _ => []
  | e :: es, i =>
    if !(Nat.beq i 0) && Nat.beq (pc24 e e) e0 then i :: invFrom e0 es (i + 1)
    else invFrom e0 es (i + 1)

@[expose] noncomputable def pairK (m : Nat) (P : List Nat) (p q c r j : Nat) : Bool :=
  (pc24 p q == pc24 q p) == c.testBit j &&
    (!c.testBit j || (decide (Nat.land (Nat.shiftRight r (8 * j)) 255 ≤ m) &&
      pc24 p q == P.getD (Nat.land (Nat.shiftRight r (8 * j)) 255) 0))

@[expose] noncomputable def tabsK (m : Nat) (P : List Nat) (D : List (Nat × Nat)) : Bool :=
  (List.range m).all fun i => (List.range m).all fun j =>
    pairK m P (P.getD i 0) (P.getD j 0) (cmD D i) (mkD D i) j

@[expose] noncomputable def permP (p x : Nat) : Nat :=
  CFSG.Quasithin.H.Mathieu.actM ((List.range 24).map fun j => 2 ^ pg 5 (mask 5) p j) x

@[expose] noncomputable def actP (cc lift : List Nat) (p m : Nat) : Nat :=
  CFSG.Quasithin.H.Mathieu.actM cc (permP p (CFSG.Quasithin.H.Mathieu.actM lift m))

@[expose] noncomputable def matP (cc lift : List Nat) (n p : Nat) : List Nat :=
  CFSG.Quasithin.H.Mathieu.matOf n (actP cc lift p)

end CFSG.KC.HMathieu

end
