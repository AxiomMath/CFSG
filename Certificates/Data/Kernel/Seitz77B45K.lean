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

@[expose] def lenF (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m a b : Nat) : Nat :=
  let cenB := (List.range 256).filter fun d => mt b d == mt d b
  let cenBp := (List.range 4).map fun p => byLabel lab m p cenB
  let swB := (List.range 256).filter fun d => mt b d == mt d a
  let swBp := (List.range 4).map fun p => byLabel lab m p swB
  (((List.range 256).filter fun c => mt a c == mt c a).map fun c =>
      (cenBp.getD (lab c) []).length).sum +
    (((List.range 256).filter fun c => mt a c == mt c b).map fun c =>
      (swBp.getD (lab c) []).length).sum

@[expose] def inv2 (mt : Nat → Nat → Nat) (w : WEl) : Bool := w != wone && wmul mt w w == wone

@[expose] def o2F (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m a b : Nat) : Nat :=
  let cenB := (List.range 256).filter fun d => mt b d == mt d b
  let cenBp := (List.range 4).map fun p => byLabel lab m p cenB
  let swB := (List.range 256).filter fun d => mt b d == mt d a
  let swBp := (List.range 4).map fun p => byLabel lab m p swB
  (((List.range 256).filter fun c => mt a c == mt c a).map fun c =>
      ((cenBp.getD (lab c) []).filter fun d => inv2 mt (c, d, false)).length).sum +
    (((List.range 256).filter fun c => mt a c == mt c b).map fun c =>
      ((swBp.getD (lab c) []).filter fun d => inv2 mt (c, d, true)).length).sum

@[expose] def cenQ (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m a b : Nat) (w : WEl) : Bool :=
  !w.2.2 &&
    ((List.range 256).filter fun c => mt a c == mt c a).all (fun c => mt w.1 c == mt c w.1) &&
    ((List.range 256).filter fun d => mt b d == mt d b).all (fun d => mt w.2.1 d == mt d w.2.1) &&
    ((List.range 256).filter fun c => mt a c == mt c b).all (fun c => mt w.1 c == mt c w.2.1) &&
    ((List.range 256).filter fun d => mt b d == mt d a).all (fun d => mt w.2.1 d == mt d w.1)

@[expose] def zW (mt : Nat → Nat → Nat) (L : List WEl) (cq : WEl → Bool) (zt : Nat)
    (I : List Nat) : Bool :=
  decide (zt < I.length) && I.all (fun i => decide (i < L.length)) &&
    decide (I.map fun i => L.getD i wone).Nodup &&
    (I.map fun i => L.getD i wone).all fun w =>
      cq w || L.all fun v => wmul mt w v == wmul mt v w

@[expose] def zwL (ZW : List (List Nat)) (a b : Nat) : List Nat :=
  ((ZW.find? fun e => e.getD 0 0 == a && e.getD 1 0 == b).getD []).drop 2

@[expose] def condL (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m len : Nat) (os : List Nat)
    (zt : Nat) (ZW : List (List Nat)) (a b : Nat) : Bool :=
  (a == 0 && b == 0) || !(inM m (lab a) (lab b)) || lenF mt lab m a b != len ||
    o2F mt lab m a b != os.getD 0 0 ||
    zW mt (cenList mt lab m a b) (cenQ mt lab m a b) zt (zwL ZW a b) ||
    differs mt (cenList mt lab m a b) len os zt

@[expose] def sliceL (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m len : Nat) (os : List Nat)
    (zt : Nat) (ZW : List (List Nat)) (alo ahi blo bhi : Nat) : Bool :=
  (invsF mt).all fun a => !(inR alo ahi a) || (invsF mt).all fun b =>
    !(inR blo bhi b) || condL mt lab m len os zt ZW a b

@[expose] def cj (mt : Nat → Nat → Nat) (inv : Nat → Nat) (g x : Nat) : Nat := mt (mt g x) (inv g)

@[expose] def sliceO (mt : Nat → Nat → Nat) (lab cr : Nat → Nat) (m len : Nat) (os : List Nat)
    (zt : Nat) (ZW : List (List Nat)) (alo ahi blo bhi : Nat) : Bool :=
  (invsF mt).all fun a => !(inR alo ahi a) || !(cr a == a) || (invsF mt).all fun b =>
    !(inR blo bhi b) || !(cr b == b) || condL mt lab m len os zt ZW a b

@[expose] def grpOK (mt : Nat → Nat → Nat) (inv : Nat → Nat) (ladd : Nat → Nat → Nat) : Bool :=
  ((List.range 256).all fun x => mt 0 x == x && mt x 0 == x && decide (inv x < 256) &&
    mt x (inv x) == 0 && mt (inv x) x == 0) &&
  (List.range 4).all fun p => ladd 0 p == p && ladd p 0 == p

@[expose] def orbOK (mt : Nat → Nat → Nat) (inv lab cr cg : Nat → Nat) : Bool :=
  (invsF mt).all fun a => decide (cr a < 256) && decide (cg a < 256) && lab (cg a) == 0 &&
    mt (cr a) (cr a) == 0 && cr (cr a) == cr a && cj mt inv (cg a) (cr a) == a

@[expose] def coversF (i a b : Nat) (s : List Nat) : Bool :=
  s.getD 0 0 == i && inR (s.getD 1 0) (s.getD 2 0) a && inR (s.getD 3 0) (s.getD 4 0) b

@[expose] def coverOKF (mt : Nat → Nat → Nat) (nm : Nat) (SL : List (List Nat)) : Bool :=
  (List.range nm).all fun i => (invsF mt).all fun a => (invsF mt).all fun b =>
    SL.any (coversF i a b)

@[expose] def coverO (mt : Nat → Nat → Nat) (cr : Nat → Nat) (nm : Nat) (SL : List (List Nat)) :
    Bool :=
  (List.range nm).all fun i => (invsF mt).all fun a => !(cr a == a) || (invsF mt).all fun b =>
    !(cr b == b) || SL.any (coversF i a b)

@[expose] def statsF (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m len : Nat) (os : List Nat)
    (zt : Nat) : Bool :=
  (tauList lab m).length == len && ordStats mt (tauList lab m) == os &&
    zOf mt (tauList lab m) == zt

@[expose] def admOK (ladd : Nat → Nat → Nat) (ms : List Nat) (lo len : Nat) : Bool :=
  (List.range' lo len).all fun m => ms.contains m || !(admM ladd m)

end CFSG.KC.SeitzB45

end
