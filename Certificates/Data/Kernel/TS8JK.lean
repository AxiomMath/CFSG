module

public import Certificates.Data.Kernel.TS8WrK
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.TS8JK

open CFSG.KC.TS8WrK

@[expose] noncomputable def pidK : Nat := CFSG.KC.Enum.pidn 820 10

@[expose] noncomputable def cK (p : Nat) : Bool :=
  CFSG.KS.Prim.canonK 820 10 (CFSG.KS.mask 10) (820 * 10) p

@[expose] noncomputable def pc (p q : Nat) : Nat := CFSG.KC.Enum.pcomp 820 10 (CFSG.KS.mask 10) p q

@[expose] noncomputable def f8 (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 8 i)) 255

@[expose] noncomputable def mK (M : Nat → Nat) (a b : Nat) : Nat := f8 (M a) b

@[expose] noncomputable def recR (E G : Nat → Nat) (RP lo cnt : Nat) : Bool :=
  CFSG.KC.TS8WrK.allN cnt fun j => letB (Nat.add lo j) fun i => CFSG.KC.TS8WrK.allN 3 fun k =>
    letB (f8 RP (Nat.add (Nat.mul 3 i) k)) fun r =>
      andB (Nat.blt r 256) (Nat.beq (E r) (pc (E i) (G k)))

@[expose] noncomputable def treeOK (E : Nat → Nat) (RP PA LA : Nat) : Bool :=
  andB (Nat.beq (E 0) pidK) (CFSG.KC.TS8WrK.allN 255 fun j =>
    letB (Nat.succ j) fun i => letB (f8 PA i) fun p => letB (f8 LA i) fun l =>
      andB (Nat.blt p i) (andB (Nat.blt l 3) (Nat.beq (f8 RP (Nat.add (Nat.mul 3 p) l)) i)))

@[expose] noncomputable def rowM (RP PA LA a r : Nat) : Bool :=
  andB (Nat.beq (f8 r 0) a) (CFSG.KC.TS8WrK.allN 255 fun j =>
    letB (Nat.succ j) fun b =>
      Nat.beq (f8 r b) (f8 RP (Nat.add (Nat.mul 3 (f8 r (f8 PA b))) (f8 LA b))))

@[expose] noncomputable def mtR (M : Nat → Nat) (RP PA LA lo cnt : Nat) : Bool :=
  CFSG.KC.TS8WrK.allN cnt fun j => letB (Nat.add lo j) fun a => letB (M a) fun r =>
    rowM RP PA LA a r

@[expose] noncomputable def ivOK (M : Nat → Nat) (IV : Nat) : Bool :=
  CFSG.KC.TS8WrK.allN 256 fun a => letB (f8 IV a) fun v =>
    andB (Nat.blt v 256) (Nat.beq (mK M a v) 0)

@[expose] noncomputable def sortOK (E : Nat → Nat) (SO SI : Nat) : Bool :=
  andB (CFSG.KC.TS8WrK.allN 256 fun a => andB (cK (E a)) (andB (Nat.blt (f8 SO a) 256)
      (Nat.beq (f8 SI (f8 SO a)) a)))
    (CFSG.KC.TS8WrK.allN 255 fun j => Nat.blt (E (f8 SO j)) (E (f8 SO (Nat.succ j))))

@[expose] noncomputable def letK (L : Nat → Nat) (l : Nat) : Nat := L l

@[expose] noncomputable def wordK (L : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) pidK (fun l _ ih => pc (L l) ih) w

@[expose] noncomputable def genOK (L G : Nat → Nat) (GW : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => andB (Nat.beq (G k) (wordK L w)) (ih (Nat.succ k))) GW 0

@[expose] noncomputable def cwOK (L E : Nat → Nat) (CW : List Nat) (zc ac : Nat) : Bool :=
  letB (wordK L CW) fun W => Nat.beq (pc W (E zc)) (pc (E ac) W)

@[expose] noncomputable def rootsGo (M : Nat → Nat) (s : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun r _ ih lo =>
    andB (Nat.ble lo r) (andB (Nat.blt r 256) (andB (Nat.beq (mK M r r) s)
      (ih (Nat.succ r))))) l

@[expose] noncomputable def rtGo (M : Nat → Nat) (RT : List (Nat × List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun p _ ih lo =>
    andB (Nat.ble lo p.1) (andB (rootsGo M p.1 p.2 0) (ih (Nat.succ p.1)))) RT

@[expose] noncomputable def rtOK (M : Nat → Nat) (RT : List (Nat × List Nat)) : Bool :=
  andB (Nat.beq (sumLen RT) 256) (rtGo M RT 0)

@[expose] noncomputable def zRec (M : Nat → Nat) (ZA : List (Nat × List Nat)) (x : Nat)
    (p : Nat × Nat) : Bool :=
  orB (Nat.beq x 0) (andB (memKey p.1 ZA) (andB (Nat.blt p.2 256)
    (Nat.beq (mK M p.2 x) (mK M p.1 p.2))))

@[expose] noncomputable def zGo (M : Nat → Nat) (ZA : List (Nat × List Nat)) (xs : List Nat) :
    List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool) (fun _ => true) (fun x _ ih zc =>
    List.rec (motive := fun _ => Bool) false (fun p tl _ => andB (zRec M ZA x p) (ih tl)) zc)
    xs

@[expose] noncomputable def zOK (M : Nat → Nat) (RT : List (Nat × List Nat))
    (ZA : List (Nat × List Nat)) (ZC : List (Nat × Nat)) : Bool :=
  zGo M ZA (rootsOf RT 0) ZC

@[expose] noncomputable def aCand (M : Nat → Nat) (z a : Nat) : Bool :=
  letB (mK M a z) fun az => letB (mK M az az) fun t =>
    andB (notB (Nat.beq t 0)) (andB (notB (Nat.beq t a)) (andB (Nat.beq (mK M t t) 0)
      (andB (Nat.beq (mK M a t) (mK M t a)) (Nat.beq (mK M z t) (mK M t z)))))

@[expose] noncomputable def aRec (M : Nat → Nat) (z : Nat) (al : List Nat) (a : Nat)
    (p : Nat × Nat) : Bool :=
  andB (memN p.1 al) (andB (Nat.blt p.2 256) (andB (Nat.beq (mK M p.2 z) (mK M z p.2))
    (Nat.beq (mK M p.2 a) (mK M p.1 p.2))))

@[expose] noncomputable def aGo (M : Nat → Nat) (z : Nat) (al : List Nat) (xs : List Nat) :
    List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool) (fun _ => true) (fun x _ ih ac =>
    List.rec (motive := fun _ => Bool) false (fun p tl _ => andB (aRec M z al x p) (ih tl)) ac)
    xs

@[expose] noncomputable def zaGo (M : Nat → Nat) (RT : List (Nat × List Nat))
    (ZA : List (Nat × List Nat)) : List (List (Nat × Nat)) → Bool :=
  List.rec (motive := fun _ => List (List (Nat × Nat)) → Bool) (fun _ => true) (fun p _ ih AC =>
    List.rec (motive := fun _ => Bool) false (fun acl tl _ =>
      andB (Nat.blt p.1 256) (andB (allL p.2 fun r => Nat.blt r 256)
        (andB (aGo M p.1 p.2 (filterL (rootsOf RT 0) (aCand M p.1)) acl) (ih tl)))) AC)
    ZA

@[expose] noncomputable def canon (M : Nat → Nat) (a t at' g : Nat) : Bool :=
  andB (Nat.blt g (mK M g a)) (andB (Nat.blt g (mK M g t)) (Nat.blt g (mK M g at')))

@[expose] noncomputable def dOK (M : Nat → Nat) (z a t c : Nat) : Bool :=
  andB (Nat.beq (mK M c a) (mK M a c)) (andB (Nat.beq (mK M c t) (mK M t c))
    (letB (mK M (mK M z c) z) fun h => Nat.beq (mK M c h) (mK M h c)))

@[expose] noncomputable def pairsOK (M : Nat → Nat) (z t at' : Nat) (R : List Nat) : Bool :=
  allL R fun g₁ => allL R fun g₂ =>
    notB (andB (Nat.beq (mK M g₁ g₂) (mK M at' (mK M g₂ g₁)))
      (letB (mK M (mK M z g₂) z) fun h₂ =>
        Nat.beq (mK M g₁ h₂) (mK M t (mK M h₂ g₁))))

@[expose] noncomputable def rowOK (M : Nat → Nat) (RT : List (Nat × List Nat)) (zc ac z a : Nat) :
    Bool :=
  orB (andB (Nat.beq z zc) (Nat.beq a ac))
    (letB (mK M a z) fun az => letB (mK M az az) fun t => letB (mK M a t) fun at' =>
      pairsOK M z t at' (filterL (appL (rootsOf RT 0) (rootsOf RT t)) fun c =>
        andB (canon M a t at' c) (dOK M z a t c)))

@[expose] noncomputable def rowsOK (M : Nat → Nat) (RT : List (Nat × List Nat)) (zc ac : Nat)
    (ZA : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih =>
    andB (allL p.2 fun a => rowOK M RT zc ac p.1 a) ih) ZA

end CFSG.KC.TS8JK
