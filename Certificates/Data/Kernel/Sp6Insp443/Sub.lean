module

public import Certificates.Data.Kernel.Sp6Insp443.Cent
public import Certificates.Data.Kernel.KGC31P

public section

namespace CFSG.KS.Sp6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P

variable (n w : Nat)

@[expose] noncomputable def packL (l : List UInt32) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun v _ ih => Nat.add (UInt32.toNat v) (Nat.shiftLeft ih w)) l

@[expose] noncomputable def packT (T : CFSG.Sporadic.Th.Native.Table) : Nat := packL w T.toList

@[expose] noncomputable def tabK (T : CFSG.Sporadic.Th.Native.Table) : Bool :=
  strictB (packT w T) (fun p => bAnd(Nat.beq T.size n, bAnd(tabPK n w (mask w) p T,
    permOK n w (mask w) (n * w) p (pinvS n w (mask w) p))))

@[expose] noncomputable def tabsK : List CFSG.Sporadic.Th.Native.Table → Bool :=
  List.rec (motive := fun _ => Bool) true (fun T _ ih => bAnd(tabK n w T, ih))

@[expose] noncomputable def pinSp (bs : List Nat) (t : Nat) : Bool :=
  (pspan n w bs).any fun u => Nat.beq u t

@[expose] noncomputable def pcommL (bs : List Nat) (t : Nat) : Bool :=
  bs.all fun b => Nat.beq (pc n w t b) (pc n w b t)

@[expose] noncomputable def pconjL (bs cs : List Nat) (t : Nat) : Bool :=
  bs.all fun b => (pspan n w cs).any fun u => Nat.beq (pc n w t b) (pc n w u t)

@[expose] noncomputable def pspanEq (bs cs : List Nat) : Bool :=
  (bs.all fun b => pinSp n w cs b) && cs.all fun c => pinSp n w bs c

@[expose] noncomputable def psubOK (us ws : List Nat) : Bool :=
  pebasis n w us && pebasis n w ws && (us.all fun u => pinSp n w ws u) &&
    ws.all fun v => pcommL n w us v

@[expose] def swapR (r : Nat) : Nat := if r = 0 then 1 else if r = 1 then 0 else r

@[expose] noncomputable def psixE (ws : List Nat) (ds : List (List Nat)) (hs : List Nat)
    (a g h : Nat) : Bool :=
  pebasis n w ws && ws.length == 5 && ds.length == 6 &&
    (ds.all fun D => pebasis n w D && D.length == 4 && D.all fun b => pinSp n w ws b) &&
    ((List.range 6).all fun r => (List.range 6).all fun s =>
      r == s || !(pspanEq n w (ds.getD r []) (ds.getD s []))) &&
    pebasis n w hs && hs.length == 4 && (hs.all fun b => pinSp n w ws b) &&
    Nat.beq (pc n w a a) (pidn n w) && pconjL n w ws ws a && pcommL n w hs a &&
    !(pcommL n w ws a) && pconjL n w ws ws g && pconjL n w ws ws h &&
    ((List.range 6).all fun r => pconjL n w (ds.getD r []) (ds.getD (swapR r) []) g) &&
    ((List.range 6).all fun r => pconjL n w (ds.getD r []) (ds.getD ((r + 1) % 6) []) h)

@[expose] noncomputable def hitsL (L ws rs : List Nat) : Bool :=
  ws.length == rs.length &&
    (ws.zip rs).all fun p => decide (p.2 < 2 ^ L.length) && Nat.beq (pmask n w L p.2) p.1

@[expose] noncomputable def pirrW (m x xi : Nat) (us ws : List Nat) (R : List (List Nat)) : Bool :=
  (List.range (2 ^ ws.length)).all fun k =>
    pinSp n w us (pmask n w ws k) ||
      hitsL n w (us ++ porbTabs n w m x xi (pmask n w ws k)) ws (R.getD k [])

end CFSG.KS.Sp6I

end
