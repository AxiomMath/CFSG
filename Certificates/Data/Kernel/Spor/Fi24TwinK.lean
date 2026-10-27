module

public import Certificates.Data.Kernel.Spor.Fi24ThreeO

public section

namespace CFSG.KC.Fi24TwinK

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Fi24Net
  CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO

@[expose] noncomputable def nthL {α : Type} (d : α) (l : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih j => Nat.rec (motive := fun _ => α) a (fun k _ => ih k) j) l i

@[expose] noncomputable def pt (F i : Nat) : Nat := fld(F, Nat.mul i (nat_lit 19), nat_lit 524287)

@[expose] noncomputable def ent (T i : Nat) : Nat := fld(T, Nat.mul i (nat_lit 11), nat_lit 2047)

@[expose] noncomputable def hiOf (m : Nat) : Nat := Nat.succ (Nat.shiftRight m (nat_lit 6))

@[expose] noncomputable def mkT (m : Nat) (f : Nat → Nat) : Nat :=
  sumBelow m (hiOf m) (fun i => Nat.shiftLeft (f i) (Nat.mul i (nat_lit 11)))

@[expose] noncomputable def cmpT (m A B : Nat) : Nat := mkT m (fun i => ent A (ent B i))

@[expose] noncomputable def idT (m : Nat) : Nat := mkT m (fun i => i)

@[expose] noncomputable def wT (m : Nat) (L : List Nat) (u : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (idT m)
    (fun l _ ih => strictN ih (fun t => cmpT m (nthL 0 L l) t)) u

@[expose] noncomputable def eqL (u v : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun v => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) v)
    (fun a _ ih v => List.rec (motive := fun _ => Bool) false (fun b t _ => andB (Nat.beq a b) (ih t)) v)
    u v

@[expose] noncomputable def plF (m F : Nat) : Nat :=
  sumBelow m (hiOf m) (fun i => Nat.shiftLeft (nat_lit 1) (pt F i))

@[expose] noncomputable def jk (m F T k : Nat) : Nat :=
  sumBelow m (hiOf m) (fun i =>
    nIf(Nat.beq (bitN (ent T i) k) (nat_lit 1), Nat.shiftLeft (nat_lit 1) (pt F i), nat_lit 0))

@[expose] noncomputable def fsOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (w : List Nat) (m F : Nat) :
    Bool :=
  andB (Nat.beq (plF m F) (fixC NW NT w))
    (andB (allBelow (Nat.sub m (nat_lit 1)) (hiOf m) (fun i => Nat.blt (pt F i) (pt F (Nat.succ i))))
      (andB (Nat.beq (pt F (nat_lit 0)) (nat_lit 0))
        (andB (Nat.ble m (nat_lit 2048)) (Nat.ble (nat_lit 1) m))))

@[expose] noncomputable def tabOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (m F : Nat) (cs : List Nat)
    (T : Nat) : Bool :=
  letB (plF m F) (fun P =>
    andB (Nat.beq (Nat.land (wkC NW NT cs P) P) P)
      (letB (idT m) (fun I =>
        allBelow (nat_lit 11) (nat_lit 1) (fun k =>
          Nat.beq (Nat.land (wkC NW NT cs (jk m F I k)) P) (jk m F T k)))))

@[expose] noncomputable def nthP (l : List (Nat × Nat)) (i : Nat) : Nat × Nat := nthL (0, 0) l i

@[expose] noncomputable def cBuild (m : Nat) (C : List (Nat × Nat)) (cd : List (Nat × Nat)) :
    List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat) → List (Nat × Nat)) (fun C => C)
    (fun e _ ih C =>
      (fun x y => ih (C ++ [(ent x.2 y.1, cmpT m (cmpT m x.2 y.2) x.2)])) (nthP C e.1) (nthP C e.2))
    cd C

@[expose] noncomputable def cdOK (n : Nat) (cd : List (Nat × Nat)) : Bool :=
  allI (fun k e => andB (Nat.blt e.1 (Nat.add n k)) (Nat.blt e.2 (Nat.add n k))) cd (nat_lit 0)

@[expose] noncomputable def eqB (a b : Bool) : Bool := bIf(a, b, notB b)

@[expose] noncomputable def rowOK (m T0 p T : Nat) : Bool :=
  andB (notB (Nat.beq (ent T0 p) p))
    (allBelow m (hiOf m) (fun i => orB (Nat.beq i (nat_lit 0)) (orB (Nat.beq i p)
      (eqB (Nat.beq (ent T0 i) i) (Nat.beq (ent T i) i)))))

@[expose] noncomputable def plC (F : Nat) (C : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (pt F e.1)) ih) C

@[expose] noncomputable def k2OK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (m F : Nat)
    (xt : List (List Nat)) (C : List (Nat × Nat)) : Bool :=
  letB (plF m F) (fun P => letB (fixC NW NT [nat_lit 26]) (fun FT =>
    andB (allL (fun W => letB (ptC NW NT W (nat_lit 0)) (fun t =>
        andB (andB (Nat.beq (bitN FT t) (nat_lit 1)) (Nat.beq (bitN P t) (nat_lit 1)))
          (notB (Nat.beq t (nat_lit 0))))) xt)
      (letB (List.rec (motive := fun _ => Nat) (Nat.xor P (Nat.land P FT))
          (fun W _ ih => strictN ih (fun a => Nat.land a (ctP NW NT FT W))) xt) (fun A =>
        Nat.beq (Nat.land A (plC F C)) A))))

@[expose] noncomputable def gPack (m : Nat) (ts : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun t _ ih k => Nat.lor (Nat.shiftLeft t (Nat.mul k (Nat.mul m (nat_lit 11)))) (ih (Nat.succ k)))
    ts (nat_lit 0)

@[expose] noncomputable def gAt (m G k : Nat) : Nat :=
  Nat.land (Nat.shiftRight G (Nat.mul k (Nat.mul m (nat_lit 11)))) (ones (Nat.mul m (nat_lit 11)))

@[expose] noncomputable def gTabs (m : Nat) (L : List Nat) (gw : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun u _ ih => wT m L u :: ih) gw

@[expose] noncomputable def revL (u : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun a _ ih => ih ++ [a]) u

@[expose] noncomputable def gTabsI (m : Nat) (L : List Nat) (gw : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun u _ ih => wT m L (revL u) :: ih) gw

@[expose] noncomputable def sT (m G GI : Nat) (v : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (idT m)
    (fun e _ ih => strictN ih (fun t => cmpT m
      (nIf(Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 0), gAt m G (Nat.shiftRight e (nat_lit 1)),
        gAt m GI (Nat.shiftRight e (nat_lit 1)))) t)) v

@[expose] noncomputable def nmOK (m : Nat) (L : List Nat) (G GI ng : Nat) (nw : List (List (List Nat)))
    : Bool :=
  allI (fun c row => andB (Nat.beq (lenL row) ng) (letB (nthL 0 L c) (fun Lc =>
    allI (fun k v => andB (allL (fun e => Nat.blt (Nat.shiftRight e (nat_lit 1)) ng) v)
      (Nat.beq (cmpT m (cmpT m Lc (gAt m G k)) Lc) (sT m G GI v))) row (nat_lit 0))))
    nw (nat_lit 0)

@[expose] noncomputable def c2OK (m G GI ng : Nat) (ab : Bool) : Bool :=
  allBelow ng (nat_lit 1) (fun i => allBelow ng (nat_lit 1) (fun j =>
    orB (Nat.ble j i)
      (bIf(ab, Nat.beq (cmpT m (gAt m G i) (gAt m G j)) (cmpT m (gAt m G j) (gAt m G i)),
        letB (cmpT m (cmpT m (gAt m GI i) (gAt m GI j)) (cmpT m (gAt m G i) (gAt m G j))) (fun Cij =>
          allBelow ng (nat_lit 1) (fun l =>
            Nat.beq (cmpT m Cij (gAt m G l)) (cmpT m (gAt m G l) Cij)))))))

@[expose] noncomputable def nmChk (m : Nat) (L : List Nat) (gw : List (List Nat))
    (nw : List (List (List Nat))) : Bool :=
  letB (gPack m (gTabs m L gw)) (fun G => letB (gPack m (gTabsI m L gw)) (fun GI =>
    andB (Nat.ble (lenL nw) (lenL L)) (nmOK m L G GI (lenL gw) nw)))

@[expose] noncomputable def c2Chk (m : Nat) (L : List Nat) (gw : List (List Nat)) (ab : Bool) : Bool :=
  letB (gPack m (gTabs m L gw)) (fun G => letB (gPack m (gTabsI m L gw)) (fun GI =>
    c2OK m G GI (lenL gw) ab))

@[expose] noncomputable def gtOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (F : Nat)
    (C : List (Nat × Nat)) (gt : List (List Nat)) : Bool :=
  andB (Nat.beq (Nat.succ (lenL gt)) (lenL C))
    (allI (fun k g => andB (Nat.beq (ptC NW NT g (nat_lit 0)) (nat_lit 0))
      (Nat.beq (ptC NW NT g (pt F (nthP C (Nat.succ k)).1)) (nat_lit 305530))) gt (nat_lit 0))

end CFSG.KC.Fi24TwinK

end
