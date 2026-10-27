module

public import Certificates.Data.Seitz77CaseB45Data
public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.SeitzB45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw Certificates.Seitz77CaseB45

@[expose] noncomputable def mtB (P : Nat → Nat) (i j : Nat) : Nat :=
  if 256 * i + j < 65536 then pg 8 (mask 8) (P ((256 * i + j) / 256)) ((256 * i + j) % 256) else 0

@[expose] noncomputable def vB (V i : Nat) : Nat := if i < 256 then pg 8 (mask 8) V i else 0

@[expose] noncomputable def rsB (R p : Nat) : Nat := if p < 4 then pg 8 (mask 8) R p else 0

@[expose] noncomputable def uB (U i : Nat) : Bool := vB U i == 1

@[expose] noncomputable def laddB (P : Nat → Nat) (L R : Nat) (p q : Nat) : Nat :=
  vB L (mtB P (rsB R p) (rsB R q))

@[expose] def invsF (mt : Nat → Nat → Nat) : List Nat := (List.range 256).filter fun i => mt i i == 0

@[expose] def condF (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m len : Nat) (os : List Nat)
    (zt a b : Nat) : Bool :=
  (a == 0 && b == 0) || !(inM m (lab a) (lab b)) || differs mt (cenList mt lab m a b) len os zt

@[expose] def inR (lo hi x : Nat) : Bool := decide (lo ≤ x) && decide (x < hi)

@[expose] def sliceF (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m len : Nat) (os : List Nat)
    (zt alo ahi blo bhi : Nat) : Bool :=
  (invsF mt).all fun a => !(inR alo ahi a) || (invsF mt).all fun b =>
    !(inR blo bhi b) || condF mt lab m len os zt a b

@[expose] def coversF (i a b : Nat) (s : List Nat) : Bool :=
  s.getD 0 0 == i && inR (s.getD 1 0) (s.getD 2 0) a && inR (s.getD 3 0) (s.getD 4 0) b

@[expose] def coverOKF (mt : Nat → Nat → Nat) (nm : Nat) (SL : List (List Nat)) : Bool :=
  (List.range nm).all fun i => (invsF mt).all fun a => (invsF mt).all fun b =>
    SL.any (coversF i a b)

@[expose] def statsF (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m len : Nat) (os : List Nat)
    (zt : Nat) : Bool :=
  (tauList lab m).length == len && ordStats mt (tauList lab m) == os &&
    zOf mt (tauList lab m) == zt

@[expose] def admOK (ladd : Nat → Nat → Nat) (ms : List Nat) (lo len : Nat) : Bool :=
  (List.range' lo len).all fun m => ms.contains m || !(admM ladd m)

end CFSG.KC.SeitzB45

end
