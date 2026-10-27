module

public import Certificates.Data.Kernel.HeModelK
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.KC.HeGlueK

open CFSG.KC.Enum CFSG.KS CFSG.KC.HexaK CFSG.KC.HeAutK CFSG.KC.HeModelK
open CFSG.KLie.CT (anyN andB orB notB)

@[expose] noncomputable def bindArrsK (gs : List (Array Nat)) (n w g : Nat) (G : Nat → Nat) :
    Bool :=
  CFSG.KLie.CT.andB (Nat.beq gs.toArray.size g) (allN g fun k => CFSG.KS.Raw.bindArrK gs.toArray[k]! n w (G k))

@[expose] noncomputable def invOK (n w a b : Nat) : Bool :=
  CFSG.KLie.CT.andB (permOK n w (mask w) (n * w) a b) (CFSG.KS.Prim.canonK n w (mask w) (n * w) b)

@[expose] noncomputable def conjW (n w c ci x : Nat) : Nat := mul n w c (mul n w x ci)

@[expose] noncomputable def letK (n w g : Nat) (G GI : Nat → Nat) (l : Nat) : Nat :=
  strictN (Nat.shiftRight l 1) fun j =>
    Bool.rec (motive := fun _ => Nat) (pidn n w)
      (Bool.rec (motive := fun _ => Nat) (G j) (GI j) (Nat.beq (Nat.land l 1) 1)) (Nat.blt j g)

@[expose] noncomputable def evalAcc (n w g : Nat) (G GI : Nat → Nat) (ws : List Nat) (acc : Nat) :
    Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun l _ ih a => strictN (mul n w a (letK n w g G GI l)) ih) ws acc

@[expose] noncomputable def evalK (n w g : Nat) (G GI : Nat → Nat) (ws : List Nat) : Nat :=
  evalAcc n w g G GI ws (pidn n w)

@[expose] noncomputable def relK (n w g : Nat) (G GI : Nat → Nat) (r : List Nat) : Bool :=
  Nat.beq (evalK n w g G GI r) (pidn n w)

@[expose] noncomputable def relsK (n w g : Nat) (G GI : Nat → Nat) (rs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => CFSG.KLie.CT.andB (relK n w g G GI r) ih) rs

@[expose] noncomputable def relsW (n w g : Nat) (G GI : Nat → Nat) (rs : List (List Nat))
    (f : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (relsK n w g G GI rs)
    (CFSG.KLie.CT.andB (relK n w g G GI (rs.getD f [])) (relsK n w g G GI rs)) (Nat.blt f rs.length)

@[expose] noncomputable def ord12K (n w x : Nat) : Bool :=
  strictB (mul n w x x) fun x2 => strictB (mul n w x2 x2) fun x4 =>
  strictB (mul n w x4 x2) fun x6 =>
    CFSG.KLie.CT.andB (Nat.beq (mul n w x6 x6) (pidn n w))
      (CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (Nat.beq x6 (pidn n w))) (CFSG.KLie.CT.notB (Nat.beq x4 (pidn n w))))

@[expose] noncomputable def pairG (a b k : Nat) : Nat := nIf(Nat.beq k 0, a, b)

@[expose] noncomputable def memS (N : Nat) (T S : Nat → Nat) (h x : Nat) : Bool :=
  strictB x fun x =>
  strictB (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => strictN acc fun acc =>
      strictN (Nat.add acc (Nat.shiftLeft 1 (Nat.sub (Nat.sub h i) 1))) fun c =>
        Bool.rec (motive := fun _ => Nat) acc c (CFSG.KLie.CT.andB (Nat.blt c N) (Nat.ble (T (S c)) x))) h)
    fun k => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (anyN N fun j => Nat.beq (T j) x) false
        (CFSG.KLie.CT.orB (CFSG.KLie.CT.andB (Nat.beq k 0) (Nat.blt x (T (S 0))))
          (CFSG.KLie.CT.andB (Nat.blt k N) (CFSG.KLie.CT.andB (Nat.blt (T (S k)) x)
            (CFSG.KLie.CT.orB (Nat.ble N (Nat.succ k)) (Nat.blt x (T (S (Nat.succ k)))))))))
      true (CFSG.KLie.CT.andB (Nat.blt k N) (Nat.beq (T (S k)) x))

structure GK where
  NP : Nat
  TP : Nat → Nat
  IP : Nat → Nat
  NB : Nat
  TB : Nat → Nat
  SB : Nat → Nat
  gB : Nat
  GB : Nat → Nat
  N23 : Nat
  T23 : Nat → Nat
  I23 : Nat → Nat
  g23 : Nat
  G23 : Nat → Nat
  G23I : Nat → Nat
  RE : Nat → Nat
  REI : Nat → Nat
  RF : Nat → Nat
  RFI : Nat → Nat
  CF : Nat → Nat
  CFI : Nat → Nat
  PE : Nat → Nat
  PEI : Nat → Nat
  PF : Nat → Nat
  PFI : Nat → Nat
  t0 : Nat
  t0I : Nat
  YTI : Nat
  gT : Nat
  GT : Nat → Nat
  gM : Nat
  GM : Nat → Nat
  gR : Nat
  GR : Nat → Nat
  N0 : Nat
  T0 : Nat → Nat
  N1 : Nat
  T1 : Nat → Nat
  NBC : Nat
  TBC : Nat → Nat
  G12 : Nat → Nat
  G12I : Nat → Nat
  G13 : Nat → Nat
  G13I : Nat → Nat
  PC0 : Nat → Nat
  PC0I : Nat → Nat
  PC1 : Nat → Nat
  PC1I : Nat → Nat
  gBC : Nat
  GBC : Nat → Nat
  tc : Nat
  gC : Nat
  GC : Nat → Nat

@[expose] noncomputable def xT (d : GK) : Nat := conjW 64 7 d.t0 d.t0I (d.PF 6)

@[expose] noncomputable def yT (d : GK) : Nat := conjW 64 7 d.t0 d.t0I (d.PF 7)

@[expose] noncomputable def pE (d : GK) (i : Nat) : Nat → Nat :=
  pairG (d.RE (Nat.mul 2 i)) (d.RE (Nat.add (Nat.mul 2 i) 1))

@[expose] noncomputable def pEI (d : GK) (i : Nat) : Nat → Nat :=
  pairG (d.REI (Nat.mul 2 i)) (d.REI (Nat.add (Nat.mul 2 i) 1))

@[expose] noncomputable def pF (d : GK) (i : Nat) : Nat → Nat :=
  pairG (d.RF (Nat.mul 2 i)) (d.RF (Nat.add (Nat.mul 2 i) 1))

@[expose] noncomputable def pFI (d : GK) (i : Nat) : Nat → Nat :=
  pairG (d.RFI (Nat.mul 2 i)) (d.RFI (Nat.add (Nat.mul 2 i) 1))

@[expose] noncomputable def invsK (d : GK) : Bool :=
  CFSG.KLie.CT.andB (allN 8 fun k => CFSG.KLie.CT.andB (invOK 64 7 (d.RE k) (d.REI k)) (CFSG.KLie.CT.andB (invOK 64 7 (d.RF k) (d.RFI k))
    (CFSG.KLie.CT.andB (invOK 64 7 (d.PE k) (d.PEI k)) (CFSG.KLie.CT.andB (invOK 64 7 (d.PF k) (d.PFI k))
    (CFSG.KLie.CT.andB (invOK 32 6 (d.PC0 k) (d.PC0I k)) (invOK 32 6 (d.PC1 k) (d.PC1I k)))))))
  (CFSG.KLie.CT.andB (allN 4 fun k => invOK 64 7 (d.CF k) (d.CFI k))
  (CFSG.KLie.CT.andB (allN 2 fun k => CFSG.KLie.CT.andB (invOK 32 6 (d.G12 k) (d.G12I k)) (invOK 32 6 (d.G13 k) (d.G13I k)))
  (CFSG.KLie.CT.andB (allN d.g23 fun k => invOK 64 7 (d.G23 k) (d.G23I k))
  (CFSG.KLie.CT.andB (invOK 64 7 d.t0 d.t0I) (invOK 64 7 (yT d) d.YTI)))))

@[expose] noncomputable def srcK (d : GK) (rels : List (List Nat)) : Bool :=
  CFSG.KLie.CT.andB (relsK 32 6 2 d.G12 d.G12I rels) (CFSG.KLie.CT.andB (relsK 32 6 2 d.G13 d.G13I rels)
  (CFSG.KLie.CT.andB (ord12K 32 6 (d.G12 1)) (CFSG.KLie.CT.andB (ord12K 32 6 (d.G13 1))
  (CFSG.KLie.CT.andB (Nat.beq (cntR (fun i => comm 32 6 (d.G12 1) (d.T0 i)) 0 d.N0) 12)
  (CFSG.KLie.CT.andB (Nat.beq (cntR (fun i => comm 32 6 (d.G13 1) (d.T1 i)) 0 d.N1) 12)
  (CFSG.KLie.CT.andB (allN 8 fun k => inL d.NP d.TP (d.RE k)) (allN 8 fun k => inL d.NP d.TP (d.RF k))))))))

@[expose] noncomputable def conjP (d : GK) (p x y : Nat) : Bool :=
  strictB (d.TP p) fun c => strictB (d.TP (d.IP p)) fun ci =>
    CFSG.KLie.CT.andB (Nat.blt p d.NP) (CFSG.KLie.CT.andB (Nat.blt (d.IP p) d.NP) (CFSG.KLie.CT.andB (invOK 64 7 c ci)
      (Nat.beq (conjW 64 7 c ci x) y)))

@[expose] noncomputable def classBAt (d : GK) (W : Nat → Nat) (j : Nat) : Bool :=
  strictB (d.TP j) fun h => CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (ord12K 64 7 h))
    (strictB (W j) fun c =>
      conjP d (Nat.shiftRight c 2) (d.RE (Nat.add (Nat.mul 2 (Nat.land c 3)) 1)) h)

@[expose] noncomputable def classCAt (d : GK) (rels : List (List Nat)) (WR W : Nat → Nat)
    (i j : Nat) : Bool :=
  strictB (d.TP j) fun h => strictB (d.TP (d.IP j)) fun hi =>
  strictB (d.RE (Nat.add (Nat.mul 2 i) 1)) fun r =>
  strictB (Nat.add (Nat.mul i d.NP) j) fun ij =>
    CFSG.KLie.CT.andB (Nat.blt (d.IP j) d.NP) (CFSG.KLie.CT.andB (invOK 64 7 h hi)
    (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (relsW 64 7 2 (pairG h r) (pairG hi (d.REI (Nat.add (Nat.mul 2 i) 1))) rels (WR ij)))
      (strictB (W ij) fun c => strictB (Nat.shiftRight c 2) fun p =>
        strictB (Nat.land c 3) fun i' => CFSG.KLie.CT.andB (conjP d p (d.RE (Nat.mul 2 i')) h)
          (conjP d p (d.RE (Nat.add (Nat.mul 2 i') 1)) r))))

@[expose] noncomputable def repFK (d : GK) : Bool :=
  allN 4 fun j => strictB (d.CF j) fun c => strictB (d.CFI j) fun ci => CFSG.KLie.CT.andB (inL d.NP d.TP c)
    (CFSG.KLie.CT.andB (Nat.beq (conjW 64 7 c ci (d.RE (Nat.mul 2 j))) (d.RF (Nat.mul 2 j)))
      (Nat.beq (conjW 64 7 c ci (d.RE (Nat.add (Nat.mul 2 j) 1))) (d.RF (Nat.add (Nat.mul 2 j) 1))))

@[expose] noncomputable def inB (d : GK) (x : Nat) : Bool := memS d.NB d.TB d.SB 10 x

@[expose] noncomputable def wordsBK (d : GK) (ws : List (List Nat)) : Bool :=
  allN 4 fun i => List.rec (motive := fun _ => Bool) true
    (fun w _ ih => CFSG.KLie.CT.andB (inB d (evalK 64 7 2 (pE d i) (pEI d i) w))
      (CFSG.KLie.CT.andB (inB d (evalK 64 7 2 (pF d i) (pFI d i) w)) ih)) ws

@[expose] noncomputable def normAt (d : GK) (j : Nat) : Bool :=
  strictB (d.TP j) fun x => strictB (d.TP (d.IP j)) fun xi =>
    CFSG.KLie.CT.andB (Nat.blt (d.IP j) d.NP) (CFSG.KLie.CT.andB (invOK 64 7 x xi)
      (allN d.gB fun k => inB d (conjW 64 7 x xi (d.GB k))))

@[expose] noncomputable def normCnt (d : GK) (lo len : Nat) : Nat := cntR (normAt d) lo len

@[expose] noncomputable def classOK (d : GK) (m : Nat) (X : Nat → Nat) (a b : Nat) : Bool :=
  CFSG.KLie.CT.andB (Nat.blt 0 m) (CFSG.KLie.CT.andB (allN m fun s => Nat.blt (X s) d.N23) (CFSG.KLie.CT.andB (Nat.beq (d.T23 (X 0)) a)
  (CFSG.KLie.CT.andB (allN m fun s => CFSG.KLie.CT.notB (Nat.beq (d.T23 (X s)) b))
    (allN m fun s => strictB (d.T23 (X s)) fun x => allN d.g23 fun k =>
      strictB (conjW 64 7 (d.G23 k) (d.G23I k) x) fun y =>
        anyN m fun t => Nat.beq (d.T23 (X t)) y))))

@[expose] noncomputable def conj23 (d : GK) (q x y : Nat) : Bool :=
  strictB (d.T23 q) fun c => strictB (d.T23 (d.I23 q)) fun ci =>
    CFSG.KLie.CT.andB (Nat.blt q d.N23) (CFSG.KLie.CT.andB (Nat.blt (d.I23 q) d.N23) (CFSG.KLie.CT.andB (invOK 64 7 c ci)
      (Nat.beq (conjW 64 7 c ci x) y)))

@[expose] noncomputable def fusK (d : GK) (wE1 wF1 wE2 wF2 : List Nat) (e : Bool) (k q m : Nat)
    (X : Nat → Nat) : Bool :=
  strictB (Nat.div (Nat.succ k) 4) fun i => strictB (Nat.mod (Nat.succ k) 4) fun j =>
  strictB (evalK 64 7 2 (pE d i) (pEI d i) wE1) fun x1 =>
  strictB (evalK 64 7 2 (pE d i) (pEI d i) wE2) fun x2 =>
  strictB (evalK 64 7 2 (pF d j) (pFI d j) wF1) fun y1 =>
  strictB (evalK 64 7 2 (pF d j) (pFI d j) wF2) fun y2 =>
  CFSG.KLie.CT.andB (Nat.beq (evalK 32 6 2 d.G12 d.G12I wE1) (evalK 32 6 2 d.G13 d.G13I wF1))
  (CFSG.KLie.CT.andB (Nat.beq (evalK 32 6 2 d.G12 d.G12I wE2) (evalK 32 6 2 d.G13 d.G13I wF2))
  (CFSG.KLie.CT.andB (Nat.beq (evalK 32 6 2 d.G13 d.G13I wE1) (evalK 32 6 2 d.G12 d.G12I wF1))
  (CFSG.KLie.CT.andB (Nat.beq (evalK 32 6 2 d.G13 d.G13I wE2) (evalK 32 6 2 d.G12 d.G12I wF2))
    (Bool.rec (motive := fun _ => Bool)
      (CFSG.KLie.CT.andB (conj23 d q y1 y2) (classOK d m X x1 x2))
      (CFSG.KLie.CT.andB (conj23 d q x1 x2) (classOK d m X y1 y2)) e))))

@[expose] noncomputable def t8 (d : GK) (hx hy k : Nat) : Nat :=
  nIf(Nat.blt k 4, d.PF k, nIf(Nat.blt k 6, pidn 64 7, nIf(Nat.beq k 6, hx, hy)))

@[expose] noncomputable def t8I (d : GK) (hxi hyi k : Nat) : Nat :=
  nIf(Nat.blt k 4, d.PFI k, nIf(Nat.blt k 6, pidn 64 7, nIf(Nat.beq k 6, hxi, hyi)))

@[expose] noncomputable def kerYAt (d : GK) (rY : List (List Nat)) (f j : Nat) : Bool :=
  strictB (d.T23 j) fun hy => strictB (d.T23 (d.I23 j)) fun hyi =>
    CFSG.KLie.CT.andB (Nat.blt (d.I23 j) d.N23) (CFSG.KLie.CT.andB (invOK 64 7 hy hyi)
      (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (relsW 64 7 8 (t8 d (pidn 64 7) hy) (t8I d (pidn 64 7) hyi) rY f))
        (CFSG.KLie.CT.orB (Nat.beq hy (d.PF 7)) (Nat.beq hy (yT d)))))

@[expose] noncomputable def kerXAt (d : GK) (rX r23 : List (List Nat)) (f f1 f2 j : Nat) : Bool :=
  strictB (d.T23 j) fun hx => strictB (d.T23 (d.I23 j)) fun hxi =>
    CFSG.KLie.CT.andB (Nat.blt (d.I23 j) d.N23) (CFSG.KLie.CT.andB (invOK 64 7 hx hxi)
      (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (relsW 64 7 8 (t8 d hx (pidn 64 7)) (t8I d hxi (pidn 64 7)) rX f))
        (CFSG.KLie.CT.andB (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (relsW 64 7 8 (t8 d hx (d.PF 7)) (t8I d hxi (d.PFI 7)) r23 f1))
            (Nat.beq hx (d.PF 6)))
          (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (relsW 64 7 8 (t8 d hx (yT d)) (t8I d hxi d.YTI) r23 f2))
            (Nat.beq hx (xT d))))))

@[expose] noncomputable def piK (d : GK) (wE wF wBE wBF : List (List Nat)) : Bool :=
  CFSG.KLie.CT.andB (allN 5 fun k =>
    strictB (nIf(Nat.blt k 4, k, 4)) fun ie => strictB (nIf(Nat.blt k 4, k, 5)) fun jf =>
    CFSG.KLie.CT.andB (Nat.beq (evalK 64 7 2 (pE d 0) (pEI d 0) (wE.getD k [])) (d.PE ie))
    (CFSG.KLie.CT.andB (Nat.beq (evalK 64 7 2 (pF d 0) (pFI d 0) (wF.getD k [])) (d.PF jf))
    (CFSG.KLie.CT.andB (Nat.beq (evalK 32 6 2 d.G12 d.G12I (wE.getD k [])) (d.PC0 ie))
    (CFSG.KLie.CT.andB (Nat.beq (evalK 32 6 2 d.G13 d.G13I (wF.getD k [])) (d.PC0 jf))
    (CFSG.KLie.CT.andB (Nat.beq (evalK 32 6 2 d.G13 d.G13I (wE.getD k [])) (d.PC1 ie))
      (Nat.beq (evalK 32 6 2 d.G12 d.G12I (wF.getD k [])) (d.PC1 jf)))))))
  (CFSG.KLie.CT.andB (Nat.beq d.gBC 4) (allN 4 fun k =>
    CFSG.KLie.CT.andB (Nat.beq (evalK 32 6 2 d.G12 d.G12I (wBE.getD k [])) (d.GBC k))
      (Nat.beq (evalK 32 6 2 d.G13 d.G13I (wBF.getD k [])) (d.GBC k))))

@[expose] noncomputable def memK (d : GK) : Bool :=
  CFSG.KLie.CT.andB (allN 4 fun k => CFSG.KLie.CT.andB (inB d (d.PE k)) (CFSG.KLie.CT.andB (inB d (d.PF k))
    (CFSG.KLie.CT.andB (inL d.NBC d.TBC (d.PC0 k)) (inL d.NBC d.TBC (d.PC1 k)))))
  (CFSG.KLie.CT.andB (inL d.NP d.TP (d.PE 4)) (CFSG.KLie.CT.andB (inL d.NP d.TP (d.PF 5))
  (CFSG.KLie.CT.andB (inL d.N0 d.T0 (d.PC0 4)) (CFSG.KLie.CT.andB (inL d.N1 d.T1 (d.PC0 5))
  (CFSG.KLie.CT.andB (inL d.N1 d.T1 (d.PC1 4)) (CFSG.KLie.CT.andB (inL d.N0 d.T0 (d.PC1 5))
  (CFSG.KLie.CT.andB (inL d.N23 d.T23 (d.PE 6)) (CFSG.KLie.CT.andB (inL d.N23 d.T23 (d.PF 6))
  (CFSG.KLie.CT.andB (inL d.N23 d.T23 (d.PE 7)) (CFSG.KLie.CT.andB (inL d.N23 d.T23 (d.PF 7))
  (CFSG.KLie.CT.andB (Nat.beq (evalK 32 6 8 d.PC0 d.PC0I [2, 4, 2, 4]) d.tc)
    (Nat.beq (evalK 32 6 8 d.PC1 d.PC1I [2, 4, 2, 4]) d.tc))))))))))))

@[expose] noncomputable def wordsEqK (n w g : Nat) (G GI : Nat → Nat) (ws : List (List Nat))
    (g' : Nat) (G' : Nat → Nat) : Bool :=
  CFSG.KLie.CT.andB (Nat.beq ws.length g') (allN g' fun k => Nat.beq (evalK n w g G GI (ws.getD k [])) (G' k))

@[expose] noncomputable def genK (d : GK) (c0 c1 wT wM wR : List (List Nat)) : Bool :=
  CFSG.KLie.CT.andB (wordsEqK 32 6 8 d.PC0 d.PC0I c0 d.gC d.GC)
  (CFSG.KLie.CT.andB (wordsEqK 32 6 8 d.PC1 d.PC1I c1 d.gC d.GC)
  (CFSG.KLie.CT.andB (wordsEqK 64 7 8 d.PE d.PEI wT d.gT d.GT) (CFSG.KLie.CT.andB (wordsEqK 64 7 8 d.PE d.PEI wM d.gM d.GM)
    (wordsEqK 64 7 8 d.PE d.PEI wR d.gR d.GR))))

@[expose] noncomputable def permsK (d : GK) : Bool :=
  permOK 32 6 (mask 6) (32 * 6) d.tc (pinvS 32 6 (mask 6) d.tc)

end CFSG.KC.HeGlueK

end
