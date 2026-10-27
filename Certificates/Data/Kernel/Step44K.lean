module

public import Certificates.Data.Kernel.HeAutK
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Tests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaTests

public section

namespace CFSG.KC.Step44K

open CFSG.KC.Enum CFSG.KS CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.KLie.CT (anyN sumN andB orB notB)
open CFSG.ComponentClassification.AS81.Hexa (sigN smSigmas f3Pairs)

@[expose] noncomputable def inV0 (PV : Nat → Nat) (x : Nat) : Bool :=
  strictB x fun x => anyN 4 fun i => Nat.beq x (PV i)

@[expose] noncomputable def fix16 (m : Nat) : Bool := allN 16 fun v => Nat.beq (pg 7 (mask 7) m v) v

@[expose] noncomputable def normV0 (PV : Nat → Nat) (m : Nat) : Bool :=
  allN 4 fun i => inV0 PV (conj 64 7 m (PV i))

@[expose] noncomputable def sixTriv (PV : Nat → Nat) (m : Nat) : Bool :=
  CFSG.KLie.CT.andB (allN 3 fun u => Nat.beq (Nat.div (pg 7 (mask 7) m (Nat.mul 16 (Nat.succ u))) 16) (Nat.succ u))
    (allN 4 fun j => Nat.beq (conj 64 7 m (PV j)) (PV j))

@[expose] noncomputable def normCount (PV : Nat → Nat) (NM : Nat) (TM : Nat → Nat) : Nat :=
  sumN NM fun j => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (normV0 PV (TM j))

@[expose] noncomputable def v0K (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NM : Nat)
    (TM : Nat → Nat) (NK : Nat) (TK : Nat → Nat) (NW : Nat) (TW : Nat → Nat) (gH : Nat)
    (GH : Nat → Nat) : Bool :=
  CFSG.KLie.CT.andB (Nat.beq (PV 0) (pidn 64 7))
  (CFSG.KLie.CT.andB (allN 4 fun i => CFSG.KLie.CT.orB (Nat.beq i 0) (CFSG.KLie.CT.notB (Nat.beq (PV i) (pidn 64 7))))
  (CFSG.KLie.CT.andB (allN 4 fun i => allN 4 fun j => Nat.beq (mul 64 7 (PV i) (PV j)) (PV (Nat.xor i j)))
  (CFSG.KLie.CT.andB (allN 4 fun i => CFSG.KLie.CT.andB (inL NM TM (PV i)) (fix16 (PV i)))
  (CFSG.KLie.CT.andB (allN NM fun k => strictB (TM k) fun m => CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (fix16 m)) (inV0 PV m))
  (CFSG.KLie.CT.andB (inL NM TM Om)
  (CFSG.KLie.CT.andB (allN 64 fun v => CFSG.KLie.CT.orB (Nat.beq v 0) (CFSG.KLie.CT.notB (Nat.beq (pg 7 (mask 7) Om v) v)))
  (CFSG.KLie.CT.andB (Nat.beq (pw 64 7 Om 3) (pidn 64 7))
  (CFSG.KLie.CT.andB (allN 4 fun i => comm 64 7 Om (PV i))
  (CFSG.KLie.CT.andB (inL NM TM Mu) (CFSG.KLie.CT.andB (Nat.beq (pw 64 7 Mu 3) (pidn 64 7)) (CFSG.KLie.CT.andB (comm 64 7 Mu Om)
  (CFSG.KLie.CT.andB (allN 4 fun i => CFSG.KLie.CT.andB (Nat.blt (MP i) 4) (Nat.beq (conj 64 7 Mu (PV i)) (PV (MP i))))
  (CFSG.KLie.CT.andB (allN NK fun k => strictB (TK k) fun x => anyN 4 fun i => inL NW TW (mul 64 7 (PV i) x))
  (CFSG.KLie.CT.andB (allN NK fun k => inV0 PV (pw 64 7 (TK k) 9))
  (CFSG.KLie.CT.andB (allN NM fun k => strictB (TM k) fun m =>
    CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (CFSG.KLie.CT.andB (normV0 PV m) (inV0 PV (pw 64 7 m 9)))) (inL NK TK m))
  (CFSG.KLie.CT.andB (Nat.beq (normCount PV NM TM) 144)
  (CFSG.KLie.CT.andB (allN gH fun k => CFSG.KLie.CT.andB (inL NM TM (GH k)) (normV0 PV (GH k)))
  (CFSG.KLie.CT.andB (allN NM fun k => strictB (TM k) fun m =>
    CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (normV0 PV m)) (allN 16 fun v => Nat.blt (pg 7 (mask 7) m v) 16))
    (allN NM fun k => strictB (TM k) fun m =>
      CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (CFSG.KLie.CT.andB (normV0 PV m) (sixTriv PV m))) (inV0 PV m))))))))))))))))))))

@[expose] noncomputable def starK (PV : Nat → Nat) (i j : Nat) : Nat :=
  Nat.add (Nat.xor (Nat.mod i 64) (pg 7 (mask 7) (PV (Nat.div i 64)) (Nat.mod j 64)))
    (Nat.mul 64 (Nat.xor (Nat.div i 64) (Nat.div j 64)))

@[expose] noncomputable def omuK (Om Mu a b : Nat) : Nat :=
  mul 64 7 (pw 64 7 Om (Nat.mod a 3)) (pw 64 7 Mu (Nat.mod b 3))

@[expose] noncomputable def muPiK (MP : Nat → Nat) (b m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) m (fun _ acc => MP acc) b

@[expose] noncomputable def tauO (MP : Nat → Nat) (o b i : Nat) : Nat :=
  Nat.add (pg 7 (mask 7) o (Nat.mod i 64)) (Nat.mul 64 (muPiK MP (Nat.mod b 3) (Nat.div i 64)))

@[expose] noncomputable def tauK (Om Mu : Nat) (MP : Nat → Nat) (a b i : Nat) : Nat :=
  tauO MP (omuK Om Mu a b) b i

@[expose] noncomputable def compK (Om Mu : Nat) (MP : Nat → Nat) (s1 s2 d : Nat × Nat)
    (y code : Nat) : Nat :=
  nIf(Nat.beq code 0, nat_lit 0,
    tauK Om Mu MP (sigN s1 s2 ((code - 1) * d.1, (code - 1) * d.2)).1
      (sigN s1 s2 ((code - 1) * d.1, (code - 1) * d.2)).2 y)

@[expose] noncomputable def nfK (NF j : Nat) : Nat := pg 2 (mask 2) NF j

@[expose] noncomputable def candAtK (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF : Nat)
    (s1 s2 : Nat × Nat) (y0 y1 y2 y3 i : Nat) : Nat :=
  starK PV (starK PV (starK PV (compK Om Mu MP s1 s2 (0, 1) y0 (nfK NF (4 * i)))
    (compK Om Mu MP s1 s2 (1, 0) y1 (nfK NF (4 * i + 1))))
    (compK Om Mu MP s1 s2 (0, 1) y2 (nfK NF (4 * i + 2))))
    (compK Om Mu MP s1 s2 (0, 1) y3 (nfK NF (4 * i + 3)))

@[expose] noncomputable def candK (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF : Nat)
    (s1 s2 : Nat × Nat) (y0 y1 y2 y3 : Nat) : Nat :=
  pmk 256 9 fun i => candAtK PV Om Mu MP NF s1 s2 y0 y1 y2 y3 i

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def fixK (Om Mu : Nat) (MP : Nat → Nat) (s1 s2 k : Nat × Nat) : List Nat :=
  strictL (omuK Om Mu (sigN s1 s2 k).1 (sigN s1 s2 k).2) fun o =>
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun r ih acc => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (r :: acc))
        (CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (Nat.beq r 0)) (Nat.beq (tauO MP o (sigN s1 s2 k).2 r) r))) 256 []

@[expose] noncomputable def homK (PV : Nat → Nat) (f : Nat) : Bool :=
  allN 256 fun i => allN 256 fun j =>
    Nat.beq (pg 9 (mask 9) f (starK PV i j)) (starK PV (pg 9 (mask 9) f i) (pg 9 (mask 9) f j))

@[expose] noncomputable def autK (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF NN : Nat)
    (TN : Nat → Nat) (lo len : Nat) : Bool :=
  allR (fun k => (fun s : (Nat × Nat) × (Nat × Nat) =>
    (fixK Om Mu MP s.1 s.2 (1, 0)).all fun y0 => (fixK Om Mu MP s.1 s.2 (0, 1)).all fun y1 =>
      (fixK Om Mu MP s.1 s.2 (1, 1)).all fun y2 => (fixK Om Mu MP s.1 s.2 (1, 2)).all fun y3 =>
        strictB (candK PV Om Mu MP NF s.1 s.2 y0 y1 y2 y3) fun f =>
          CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (homK PV f)) (inL NN TN f)) (smSigmas.getD k ((0, 0), (0, 0)))) lo len

@[expose] noncomputable def tauChk (PV : Nat → Nat) (Om Mu : Nat) (MP : Nat → Nat) (NF : Nat) :
    Bool :=
  CFSG.KLie.CT.andB (f3Pairs.all fun c => f3Pairs.all fun c' =>
      strictB (omuK Om Mu c.1 c.2) fun o => strictB (omuK Om Mu c'.1 c'.2) fun o' =>
        strictB (omuK Om Mu (c.1 + c'.1) (c.2 + c'.2)) fun o'' =>
          allN 256 fun i => Nat.beq (tauO MP o c.2 (tauO MP o' c'.2 i)) (tauO MP o'' (c.2 + c'.2) i))
  (CFSG.KLie.CT.andB (f3Pairs.all fun c => CFSG.KLie.CT.orB (CFSG.KLie.CT.andB (Nat.beq c.1 0) (Nat.beq c.2 0))
      (strictB (omuK Om Mu c.1 c.2) fun o => anyN 256 fun i => CFSG.KLie.CT.notB (Nat.beq (tauO MP o c.2 i) i)))
  (CFSG.KLie.CT.andB (Nat.beq (tauK Om Mu MP 1 0 64) 64) (CFSG.KLie.CT.andB (Nat.beq (tauK Om Mu MP 0 1 30) 30)
  (CFSG.KLie.CT.andB (Nat.beq (tauK Om Mu MP 1 1 4) 4) (CFSG.KLie.CT.andB (Nat.beq (tauK Om Mu MP 1 2 1) 1)
    (Nat.beq (candK PV Om Mu MP NF (1, 0) (0, 1) 64 30 4 1) (pidn 256 9)))))))

@[expose] noncomputable def presT (f : Nat) : Bool := allN 64 fun i => Nat.blt (pg 9 (mask 9) f i) 64

@[expose] noncomputable def smK (PV : Nat → Nat) (gN : Nat) (GN : Nat → Nat) (NN : Nat)
    (TN : Nat → Nat) (gE : Nat) (GE : Nat → Nat) (NE : Nat) (TE : Nat → Nat) (gP : Nat)
    (GP : Nat → Nat) (gQ : Nat) (GQ : Nat → Nat) (gY : Nat) (GY : Nat → Nat) (NAb : Nat)
    (TAb : Nat → Nat) (gX : Nat) (GX : Nat → Nat) (NAa : Nat) (TAa : Nat → Nat) : Bool :=
  CFSG.KLie.CT.andB (allN gN fun k => homK PV (GN k))
  (CFSG.KLie.CT.andB (allN gE fun k => inL NN TN (GE k))
  (CFSG.KLie.CT.andB (allN NN fun k => strictB (TN k) fun f => CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (presT f)) (inL NE TE f))
  (CFSG.KLie.CT.andB (allN gP fun k => inL NN TN (GP k)) (CFSG.KLie.CT.andB (allN gQ fun k => inL NE TE (GQ k))
  (CFSG.KLie.CT.andB (allN gY fun k => inL NAb TAb (GY k)) (allN gX fun k => inL NAa TAa (GX k)))))))

end CFSG.KC.Step44K

end
