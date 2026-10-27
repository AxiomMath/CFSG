module

public section

namespace CFSG.KC.GGToral

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def lane (v j : Nat) : Nat :=
  Nat.mod (Nat.shiftRight v (Nat.mul 16 j)) 65536

@[expose] noncomputable def row (T r : Nat) : Nat :=
  Nat.mod (Nat.shiftRight T (Nat.mul 128 r)) 340282366920938463463374607431768211456

@[expose] noncomputable def memB (m r : Nat) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 r))

@[expose] noncomputable def beqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def modL (p n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.add ih (Nat.shiftLeft (Nat.mod (lane x j) p) (Nat.mul 16 j))) n

structure Hd where
  mode : Nat
  n : Nat
  p : Nat
  np : Nat
  rrev : Nat
  adj : Nat
  cor : Nat
  atil : Nat
  threv : Nat
  k0 : Nat
  gam : Nat

@[expose] noncomputable def tw (H : Hd) : Bool := Nat.beq H.mode 1

@[expose] noncomputable def rd (k : Nat → List Nat → Bool) (s : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x xs _ => k x xs) s

@[expose] noncomputable def rdN (m : Nat) : (List Nat → List Nat → Bool) → List Nat → Bool :=
  Nat.rec (motive := fun _ => (List Nat → List Nat → Bool) → List Nat → Bool)
    (fun k s => k [] s)
    (fun _ ih => fun k s => rd (fun x s1 => ih (fun l s2 => k (x :: l) s2) s1) s) m

@[expose] noncomputable def dotR (H : Hd) (arev v : Nat) : Nat := lane (Nat.mul arev v) (Nat.sub H.n 1)

@[expose] noncomputable def killed (H : Hd) (r v : Nat) : Bool :=
  Nat.beq (Nat.mod (dotR H (row H.rrev r) v) H.p) 0

@[expose] noncomputable def zL (H : Hd) (v q : Nat) : Bool := Nat.beq (Nat.mod (lane v q) H.p) 0

@[expose] noncomputable def red (H : Hd) (v : Nat) : Bool := Nat.beq (modL H.p H.n v) v

@[expose] noncomputable def inV (H : Hd) (v : Nat) : Bool :=
  orB (notB (tw H)) (andB (Nat.beq (lane v 5) (lane v 0)) (Nat.beq (lane v 4) (lane v 2)))

@[expose] noncomputable def simple (H : Hd) (l f : Nat) : Nat :=
  modL H.p H.n (Nat.add f (Nat.mul (lane f l) (row H.atil l)))

@[expose] noncomputable def thetaL (H : Hd) (f : Nat) : Nat :=
  modL H.p H.n (Nat.add f (Nat.shiftLeft (Nat.sub H.p (Nat.mod (dotR H H.threv f) H.p))
    (Nat.mul 16 H.k0)))

@[expose] noncomputable def twLetter (H : Hd) (g f : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (simple H 5 (simple H 0 f)) (simple H 4 (simple H 2 f))
        (Nat.beq g 2))
      (simple H 3 f) (Nat.beq g 1))
    (simple H 1 f) (Nat.beq g 0)

@[expose] noncomputable def letter (H : Hd) (l f : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (thetaL H f) (simple H l f) (Nat.blt l H.n))
    (twLetter H l f) (tw H)

@[expose] noncomputable def word (H : Hd) (w : List Nat) (f : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun f => f) (fun l _ ih => fun f => ih (letter H l f)) w f

@[expose] noncomputable def ngens (H : Hd) : Nat := Bool.rec (motive := fun _ => Nat) H.n 4 (tw H)

@[expose] noncomputable def dimV (H : Hd) : Nat := Bool.rec (motive := fun _ => Nat) H.n 4 (tw H)

@[expose] noncomputable def codeP (H : Hd) (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.add (Nat.mul ih H.p) (lane v (Nat.sub (Nat.sub H.n 1) j))) H.n

@[expose] noncomputable def inM (H : Hd) (m v : Nat) : Bool := memB m (codeP H v)

@[expose] noncomputable def addM (H : Hd) (m v : Nat) : Nat := Nat.lor m (Nat.shiftLeft 1 (codeP H v))

@[expose] noncomputable def vecOK (H : Hd) (v : Nat) : Bool :=
  andB (red H v) (andB (notB (Nat.beq v 0)) (inV H v))

@[expose] noncomputable def entsK (H : Hd) (kont : Nat → List Nat → List Nat → List Nat → Bool)
    (m : Nat) : Nat → List Nat → List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → List Nat → Bool) kont
    (fun _ ih => fun mask reps ents s => rd (fun v s1 => rd (fun l s2 =>
      andB (vecOK H v)
        (andB (orB (Nat.beq l 0) (inM H mask (letter H (Nat.sub l 1) v)))
          (ih (addM H mask v)
            (Bool.rec (motive := fun _ => List Nat) reps (v :: reps) (Nat.beq l 0))
            (v :: ents) s2))) s1) s) m

@[expose] noncomputable def closedLM (H : Hd) (mask : Nat) (ents : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun v _ ih => andB
      (Nat.rec (motive := fun _ => Bool) true (fun g ihg => andB (inM H mask (letter H g v)) ihg)
        (ngens H)) ih) ents

@[expose] noncomputable def npItem (H : Hd) (mask r e t : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (Nat.blt t (Nat.add H.p (Nat.mul H.p H.p)))
      (let x := modL H.p H.n (Nat.add (Nat.mul (Nat.div (Nat.sub t H.p) H.p) r)
        (Nat.mul (Nat.mod (Nat.sub t H.p) H.p) e))
       andB (notB (Nat.beq x 0)) (notB (inM H mask x))))
    (Nat.beq e (modL H.p H.n (Nat.mul t r)))
    (Nat.blt t H.p)

@[expose] noncomputable def noPlaneK (H : Hd) (mask : Nat) (ents : List Nat) (kont : List Nat → Bool)
    (reps : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) kont
    (fun r _ ih => fun s =>
      List.rec (motive := fun _ => List Nat → Bool) ih
        (fun e _ ihe => fun s1 => rd (fun t s2 => andB (npItem H mask r e t) (ihe s2)) s1) ents s)
    reps

@[expose] noncomputable def lmK (H : Hd) (kont : Nat → List Nat → Bool) (s : List Nat) : Bool :=
  rd (fun m s1 => entsK H (fun mask reps ents s2 =>
    andB (closedLM H mask ents) (noPlaneK H mask ents (kont mask) reps s2)) m 0 [] [] s1) s

@[expose] noncomputable def lmsK (H : Hd) (m : Nat) : (List Nat → List Nat → Bool) → List Nat → Bool :=
  Nat.rec (motive := fun _ => (List Nat → List Nat → Bool) → List Nat → Bool)
    (fun k s => k [] s)
    (fun _ ih => fun k s => lmK H (fun mask s1 => ih (fun ms s2 => k (mask :: ms) s2) s1) s) m

@[expose] noncomputable def nthM (ms : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun m _ ih => fun k => Bool.rec (motive := fun _ => Nat) (ih (Nat.sub k 1)) m (Nat.beq k 0)) ms k

@[expose] noncomputable def alcB (p n : Nat) (ts : List Nat) : Nat → Nat → Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → List Nat → List Nat)
    (fun _ _ x acc =>
      let y := modL p n x
      Bool.rec (motive := fun _ => List Nat) (y :: acc) acc (Nat.beq y 0))
    (fun t _ ih => fun b j x acc =>
      Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
        (fun i ihi => fun acc => ihi (ih (Nat.sub b (Nat.mul t i)) (Nat.add j 1)
          (Nat.add x (Nat.shiftLeft i (Nat.mul 16 j))) acc))
        (Nat.add (Nat.div b t) 1) acc) ts

@[expose] noncomputable def alcNZ (p n : Nat) (theta : List Nat) : List Nat := alcB p n theta p 0 0 []

@[expose] noncomputable def twPt (p x : Nat) : Nat :=
  let d0 := Nat.mod x p
  let d1 := Nat.mod (Nat.div x p) p
  let d2 := Nat.mod (Nat.div x (Nat.mul p p)) p
  let d3 := Nat.mod (Nat.div x (Nat.mul p (Nat.mul p p))) p
  Nat.add d0 (Nat.add (Nat.shiftLeft d1 16) (Nat.add (Nat.shiftLeft d2 32)
    (Nat.add (Nat.shiftLeft d3 48) (Nat.add (Nat.shiftLeft d2 64) (Nat.shiftLeft d0 80)))))

@[expose] noncomputable def twV (p : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun i ih => fun acc => ih (Bool.rec (motive := fun _ => List Nat) (twPt p i :: acc) acc
      (Nat.beq i 0)))
    (Nat.mul p (Nat.mul p (Nat.mul p p))) []

@[expose] noncomputable def allVec (H : Hd) (T : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun v _ ih => andB (vecOK H v) ih) T

@[expose] noncomputable def maskL (H : Hd) (T : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun v _ ih => addM H ih v) T

@[expose] noncomputable def wordsK (H : Hd) (tm : Nat) (kont : List Nat → Bool) (pts : List Nat) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) kont
    (fun a _ ih => fun s => rd (fun wl s1 => rdN wl (fun w s2 =>
      andB (inM H tm (word H w a)) (ih s2)) s1) s) pts

@[expose] noncomputable def phiOK (H : Hd) (mu phi : Nat) : Bool :=
  andB (Nat.blt phi (Nat.shiftLeft 1 H.np))
    (Nat.rec (motive := fun _ => Bool) true
      (fun r ih => andB (beqB (memB phi r) (killed H r mu)) ih) H.np)

@[expose] noncomputable def maskOf (mem : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun r _ ih => Nat.lor ih (Nat.shiftLeft 1 r)) mem

@[expose] noncomputable def closedOK (H : Hd) (phi cm : Nat) (mem : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (Nat.beq (Nat.lor (Nat.land (row H.adj r) phi) cm) cm) ih) mem

@[expose] noncomputable def linkedOK (H : Hd) (mem : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih => fun pre =>
      andB (orB (Nat.beq pre 0) (notB (Nat.beq (Nat.land (row H.adj r) pre) 0)))
        (ih (Nat.lor pre (Nat.shiftLeft 1 r)))) mem 0

@[expose] noncomputable def allKilled (H : Hd) (mem : List Nat) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (killed H r v)
      (andB (orB (notB (tw H)) (killed H (lane H.gam r) v)) ih)) mem

@[expose] noncomputable def kerVec (H : Hd) (mem : List Nat) (v q : Nat) : Bool :=
  andB (red H v) (andB (inV H v) (andB (allKilled H mem v)
    (andB (Nat.blt q H.n) (notB (zL H v q)))))

@[expose] noncomputable def kerOK (H : Hd) (mem : List Nat) (v1 q1 v2 q2 v3 q3 : Nat) : Bool :=
  andB (kerVec H mem v1 q1) (andB (kerVec H mem v2 q2) (andB (kerVec H mem v3 q3)
    (andB (zL H v2 q1) (andB (zL H v3 q1) (zL H v3 q2)))))

@[expose] noncomputable def genOf (H : Hd) (mu g : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (row H.cor (Nat.sub g 1))
      (Nat.add (row H.cor (Nat.sub g 1)) (row H.cor (lane H.gam (Nat.sub g 1)))) (tw H))
    mu (Nat.beq g 0)

@[expose] noncomputable def genValid (mem : List Nat) (g : Nat) : Bool :=
  orB (Nat.beq g 0) (List.rec (motive := fun _ => Bool) false
    (fun r _ ih => orB (Nat.beq r (Nat.sub g 1)) ih) mem)

@[expose] noncomputable def combo (H : Hd) (mu : Nat) (ps : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun gc _ ih =>
      modL H.p H.n (Nat.add ih (Nat.mul (Nat.mod gc 256) (genOf H mu (Nat.div gc 256))))) ps

@[expose] noncomputable def pairsOK (H : Hd) (mem ps : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun gc _ ih => andB (genValid mem (Nat.div gc 256)) (andB (Nat.blt (Nat.mod gc 256) H.p) ih)) ps

@[expose] noncomputable def zeroAt (H : Hd) (P : List Nat) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun q _ ih => andB (zL H v q) ih) P

@[expose] noncomputable def rowsK (H : Hd) (mu : Nat) (mem : List Nat) (kont : List Nat → Bool)
    (k : Nat) : List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => List Nat → List Nat → Bool) (fun _ s => kont s)
    (fun _ ih => fun P s => rd (fun vec s1 => rd (fun piv s2 => rd (fun nco s3 =>
      rdN nco (fun ps s4 =>
        andB (Nat.beq vec (combo H mu ps)) (andB (pairsOK H mem ps)
          (andB (Nat.blt piv H.n) (andB (notB (zL H vec piv))
            (andB (zeroAt H P vec) (ih (piv :: P) s4)))))) s3) s2) s1) s) k

@[expose] noncomputable def oneWit (H : Hd) (mu : Nat) (mem : List Nat) (t : Nat)
    (kont : List Nat → Bool) (s : List Nat) : Bool :=
  rd (fun nco s1 => rdN nco (fun ps s2 => rd (fun wl s3 => rdN wl (fun w s4 =>
    let sv := combo H mu ps
    andB (pairsOK H mem ps) (andB (notB (Nat.beq sv 0))
      (andB (Nat.beq (word H w sv) t) (kont s4)))) s3) s2) s1) s

@[expose] noncomputable def witK (H : Hd) (mu : Nat) (mem : List Nat) (mask : Nat)
    (kont : List Nat → Bool) (tg : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) kont
    (fun t _ ih => fun s =>
      Bool.rec (motive := fun _ => Bool) (oneWit H mu mem t ih s) (ih s) (inM H mask t)) tg

@[expose] noncomputable def kindK (H : Hd) (tg ms : List Nat) (mu : Nat) (mem : List Nat)
    (kont : List Nat → Bool) (kind : Nat) (s : List Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq kind 3) (rd (fun k s1 => witK H mu mem (nthM ms k) kont tg s1) s))
        (witK H mu mem 0 kont tg s) (Nat.beq kind 2))
      (rd (fun nr s1 => andB (Nat.ble (dimV H) (Nat.add nr 1)) (rowsK H mu mem kont nr [] s1)) s)
      (Nat.beq kind 1))
    (rd (fun v1 s1 => rd (fun q1 s2 => rd (fun v2 s3 => rd (fun q2 s4 => rd (fun v3 s5 =>
      rd (fun q3 s6 => andB (kerOK H mem v1 q1 v2 q2 v3 q3) (kont s6)) s5) s4) s3) s2) s1) s)
    (Nat.beq kind 0)

@[expose] noncomputable def classK (H : Hd) (tg ms : List Nat) (mu phi acc : Nat)
    (kont : Nat → List Nat → Bool) (s : List Nat) : Bool :=
  rd (fun nm s1 => rdN nm (fun mem s2 => rd (fun kind s3 =>
    let cm := maskOf mem
    andB (Nat.beq (Nat.land acc cm) 0) (andB (Nat.beq (Nat.land cm phi) cm)
      (andB (notB (Nat.beq nm 0)) (andB (closedOK H phi cm mem) (andB (linkedOK H mem)
        (kindK H tg ms mu mem (kont (Nat.lor acc cm)) kind s3)))))) s2) s1) s

@[expose] noncomputable def classesK (H : Hd) (tg ms : List Nat) (mu phi : Nat)
    (kont : Nat → List Nat → Bool) (k : Nat) : Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool) kont
    (fun _ ih => fun acc s => classK H tg ms mu phi acc ih s) k

@[expose] noncomputable def muK (H : Hd) (tg ms : List Nat) (pts : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun s => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) s)
    (fun a _ ih => fun s => rd (fun mu s1 => rd (fun phi s2 => rd (fun nc s3 =>
      andB (Nat.beq mu a) (andB (phiOK H mu phi)
        (classesK H tg ms mu phi (fun acc rest => andB (Nat.beq acc phi) (ih rest)) nc 0 s3))) s2)
      s1) s) pts

@[expose] noncomputable def bodyK (H : Hd) (pts ms : List Nat) (s : List Nat) : Bool :=
  rd (fun nt s1 => rdN nt (fun T s2 =>
    Bool.rec (motive := fun _ => Bool)
      (andB (allVec H T) (wordsK H (maskL H T) (muK H T ms pts) pts s2))
      (muK H pts ms pts s2) (Nat.beq nt 0)) s1) s

@[expose] noncomputable def restK (H : Hd) (theta : List Nat) (s : List Nat) : Bool :=
  let pts := Bool.rec (motive := fun _ => List Nat) (alcNZ H.p H.n theta) (twV H.p) (tw H)
  rd (fun nr s1 => rdN nr (fun _ s2 => rd (fun nl s3 =>
    lmsK H nl (fun ms s4 => bodyK H pts ms s4) s3) s2) s1) s

@[expose] noncomputable def hdK (k : Hd → List Nat → Bool) (s : List Nat) : Bool :=
  rd (fun a0 s0 => rd (fun a1 s1 => rd (fun a2 s2 => rd (fun a3 s3 => rd (fun a4 s4 =>
    rd (fun a5 s5 => rd (fun a6 s6 => rd (fun a7 s7 => rd (fun a8 s8 => rd (fun a9 s9 =>
      rd (fun a10 s10 => k ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ s10) s9) s8) s7) s6)
      s5) s4) s3) s2) s1) s0) s

@[expose] noncomputable def pkCheck (theta : List Nat) (D : List Nat) : Bool :=
  hdK (fun H s => restK H theta s) D

@[expose] noncomputable def rootIs (H : Hd) (c r s : Nat) (k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih =>
      let d := Nat.mod (Nat.shiftRight c (Nat.mul 4 j)) 16
      let x := lane (row H.rrev r) (Nat.sub (Nat.sub H.n 1) j)
      andB (Bool.rec (motive := fun _ => Bool) (Nat.beq d (Nat.add 8 x)) (Nat.beq (Nat.add d x) 8)
        (Nat.beq s 1)) ih) k

@[expose] noncomputable def rixK (H : Hd) (codes : List Nat) : Nat → List Nat → Nat :=
  List.rec (motive := fun _ => Nat → List Nat → Nat)
    (fun m s => Bool.rec (motive := fun _ => Nat) 0 m (List.rec (motive := fun _ => Bool) true
      (fun _ _ _ => false) s))
    (fun c _ ih => fun m s => List.rec (motive := fun _ => Nat) 0
      (fun x xs _ =>
        Bool.rec (motive := fun _ => Nat) 0
          (ih (Bool.rec (motive := fun _ => Nat) m (Nat.lor m (Nat.shiftLeft 1 (Nat.div x 2)))
            (Nat.beq (Nat.mod x 2) 0)) xs)
          (andB (Nat.blt (Nat.div x 2) H.np) (andB (Nat.blt (Nat.mod x 2) 2)
            (rootIs H c (Nat.div x 2) (Nat.mod x 2) H.n)))) s) codes

@[expose] noncomputable def pkHead (codes : List Nat) (D : List Nat) : Bool :=
  hdK (fun H s => rd (fun nr s1 => rdN nr (fun R _ =>
    Nat.beq (rixK H codes 0 R) (Nat.sub (Nat.shiftLeft 1 H.np) 1)) s1) s) D

end CFSG.KC.GGToral
