module

public import CFSG.Certificates.Kernel.Common.Loop
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz U35Pk "Certificates/Data/Kernel/U35Pk/u35pk.json.gz" 53592
  3991642391515542125
  (LOW : Nat) (LMd : Nat) (M0d : Nat) (M1d : Nat) (M2d : Nat) (BLKd : Nat) (DIAG : Nat) (E : Nat)
  (RE : Nat) (LA : Nat) (OA : Nat) (RA : Nat) (SA : Nat) (R2A : Nat) (SB : Nat) (repW : List Nat)
  (nW : List Nat) (tinvL : List Nat) (tBL : List Nat) (lamL : List Nat) (cov0 : List Nat)
  (cov1 : List Nat) (cov2 : List Nat) (cov3 : List Nat) (cov4 : List Nat) (cov5 : List Nat)
  (cov6 : List Nat)

public section

namespace U35Pk

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allR (f : Nat → Bool) (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih lo => bAnd(f lo, strictB (Nat.add lo 1) ih)) n

@[expose] noncomputable def allL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def anyL (L : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(f x, true, ih)) L

@[expose] noncomputable def getK (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) L

@[expose] noncomputable def getLL (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) L

@[expose] noncomputable def lenK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def packL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor x (Nat.shiftLeft ih 2048)) L

@[expose] noncomputable def lookP (T i : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul 2048 i)) LOW

@[expose] noncomputable def red (x : Nat) : Nat :=
  Nat.sub x (Nat.mul 5 (Nat.land (Nat.shiftRight (Nat.mul x 205) 10) LMd))

@[expose] noncomputable def mulAB (a b : Nat) : Nat :=
  strictN (Nat.mul a b) fun y =>
    strictN (Nat.add (Nat.land y LOW) (Nat.shiftLeft (Nat.shiftRight y 2048) 1)) fun z =>
      strictN (Nat.lor (Nat.lor (Nat.land z M0d) (Nat.land (Nat.shiftRight z 324) M1d))
        (Nat.land (Nat.shiftRight z 648) M2d)) red

@[expose] noncomputable def isScal (c : Nat) : Bool :=
  Nat.beq c (Nat.mul (Nat.lor (Nat.land (Nat.shiftRight c 36) 255)
    (Nat.shiftLeft (Nat.land (Nat.shiftRight c 1060) 255) 1024)) DIAG)

@[expose] noncomputable def isBlk (c : Nat) : Bool := Nat.beq (Nat.land c BLKd) 0

@[expose] noncomputable def mv (c p q : Nat) : Nat := Nat.shiftLeft (Nat.land (Nat.shiftRight c p) E) q

@[expose] noncomputable def bToA (c : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (mv c 108 0) (mv c 126 54)) (Nat.lor (mv c 144 108) (mv c 54 270)))
    (Nat.lor (Nat.lor (mv c 72 324) (mv c 90 378))
      (Nat.lor (mv c 0 540) (Nat.lor (mv c 18 594) (mv c 36 648))))

@[expose] noncomputable def aToB (c : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (mv c 0 108) (mv c 54 126)) (Nat.lor (mv c 108 144) (mv c 270 54)))
    (Nat.lor (Nat.lor (mv c 324 72) (mv c 378 90))
      (Nat.lor (mv c 540 0) (Nat.lor (mv c 594 18) (mv c 648 36))))

@[expose] noncomputable def trB (c : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (mv c 108 108) (mv c 126 54)) (Nat.lor (mv c 144 0) (mv c 54 126)))
    (Nat.lor (Nat.lor (mv c 72 72) (mv c 90 18))
      (Nat.lor (mv c 0 144) (Nat.lor (mv c 18 90) (mv c 36 36))))

@[expose] noncomputable def cjB (c : Nat) : Nat :=
  Nat.add (Nat.land c RE) (red (Nat.mul 4 (Nat.land c (Nat.shiftLeft RE 1024))))

@[expose] noncomputable def canA (x : Nat) : Bool :=
  bAnd(Nat.beq (Nat.land x LA) x,
    Nat.beq (Nat.land (Nat.add x (Nat.mul 3 OA)) (Nat.mul 504 OA)) 0)

@[expose] noncomputable def unitK (MA : Nat) : Bool :=
  strictB (aToB MA) fun MB => strictB (cjB MB) fun C => strictB (trB C) fun HB =>
    Nat.beq (mulAB (bToA HB) MB) DIAG

@[expose] noncomputable def ordK (XA : Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih P j => nIf(isScal P, j, strictN (mulAB XA P) fun P' => ih P' (Nat.add j 1))) fuel

@[expose] noncomputable def inT (Q : Nat) : Bool :=
  bAnd(isBlk Q, anyL tinvL fun ti => strictB (mulAB ti Q) isScal)

@[expose] noncomputable def refK (XA : Nat) (fuel : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih Q => bIf(inT Q, false, strictB (mulAB XA Q) ih)) fuel

@[expose] noncomputable def eltK (XB : Nat) : Bool :=
  strictB (bToA XB) fun XA => strictB (ordK XA 40 XB 1) fun o =>
    bAnd(bIf(Nat.beq o 0, false, true),
      bIf(Nat.beq (Nat.land o 1) 0, true,
        bIf(bAnd(isBlk XB, bIf(Nat.beq o 5, false, true)), true,
          bIf(strictB (mulAB SA XB) (refK XA o), true,
            bIf(strictB (mulAB RA XB) (refK XA o), true, strictB (mulAB R2A XB) (refK XA o))))))

@[expose] noncomputable def ent (a0 a1 p : Nat) : Nat :=
  Nat.add (Nat.shiftLeft a0 p) (Nat.shiftLeft a1 (Nat.add p 1024))

@[expose] noncomputable def nrm2 (k : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.add (Nat.mul (Nat.mod k 5) (Nat.mod k 5))
    (Nat.mul 3 (Nat.mul (Nat.mod (Nat.div k 5) 5) (Nat.mod (Nat.div k 5) 5))))
    (Nat.add (Nat.mul (Nat.mod (Nat.div k 25) 5) (Nat.mod (Nat.div k 25) 5))
      (Nat.mul 3 (Nat.mul (Nat.mod (Nat.div k 125) 5) (Nat.mod (Nat.div k 125) 5))))) 5) 1

@[expose] noncomputable def nrm1 (c : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.mul (Nat.mod c 5) (Nat.mod c 5))
    (Nat.mul 3 (Nat.mul (Nat.div c 5) (Nat.div c 5)))) 5) 1

@[expose] noncomputable def y0B (k : Nat) : Nat :=
  Nat.add (Nat.add (ent (Nat.mod k 5) (Nat.mod (Nat.div k 5) 5) 108)
      (ent (Nat.mod (Nat.sub 5 (Nat.mod (Nat.div k 25) 5)) 5) (Nat.mod (Nat.div k 125) 5) 126))
    (Nat.add (Nat.add (ent (Nat.mod (Nat.div k 25) 5) (Nat.mod (Nat.div k 125) 5) 54)
      (ent (Nat.mod k 5) (Nat.mod (Nat.sub 5 (Nat.mod (Nat.div k 5) 5)) 5) 72)) (ent 1 0 36))

@[expose] noncomputable def dB (d : Nat) : Nat :=
  Nat.add (Nat.add (ent 1 0 108) (ent 1 0 36)) (ent (Nat.mod d 5) (Nat.div d 5) 72)

@[expose] noncomputable def gu2Step (UA k : Nat) : Bool :=
  bIf(nrm2 k, strictB (mulAB UA (y0B k)) fun ZB => strictB (bToA ZB) fun ZA =>
    allR (fun d => bIf(nrm1 d, strictB (mulAB ZA (dB d)) eltK, true)) 25 0, true)

@[expose] noncomputable def gu2R (UA lo n : Nat) : Bool :=
  strictB UA fun U => allR (gu2Step U) n lo

@[expose] noncomputable def gu2K (UA : Nat) : Bool := gu2R UA 0 625

@[expose] noncomputable def vB (v : Nat) : Nat :=
  Nat.add (Nat.add (ent (Nat.mod v 5) (Nat.mod (Nat.div v 5) 5) 144)
      (ent (Nat.mod (Nat.div v 25) 5) (Nat.mod (Nat.div v 125) 5) 90))
    (ent (Nat.mod (Nat.div v 625) 5) (Nat.mod (Nat.div v 3125) 5) 36)

@[expose] noncomputable def nrmV (v : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.add (Nat.mul (Nat.mod v 5) (Nat.mod v 5))
    (Nat.mul 3 (Nat.mul (Nat.mod (Nat.div v 5) 5) (Nat.mod (Nat.div v 5) 5))))
    (Nat.add (Nat.add (Nat.mul (Nat.mod (Nat.div v 25) 5) (Nat.mod (Nat.div v 25) 5))
      (Nat.mul 3 (Nat.mul (Nat.mod (Nat.div v 125) 5) (Nat.mod (Nat.div v 125) 5))))
      (Nat.add (Nat.mul (Nat.mod (Nat.div v 625) 5) (Nat.mod (Nat.div v 625) 5))
        (Nat.mul 3 (Nat.mul (Nat.mod (Nat.div v 3125) 5) (Nat.mod (Nat.div v 3125) 5)))))) 5) 1

@[expose] noncomputable def entOK (NP UP LP e v : Nat) : Bool :=
  bAnd(Nat.blt e 4608, Nat.beq (mulAB (lookP NP (Nat.div e 96)) (vB v))
    (mulAB (lookP UP (Nat.mod (Nat.div e 6) 16)) (lookP LP (Nat.mod e 6))))

@[expose] noncomputable def covR (NP UP LP n : Nat) : Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun _ ih k L => bIf(nrmV k,
      List.rec (motive := fun _ => Bool) false
        (fun e t _ => bAnd(entOK NP UP LP e k, strictB (Nat.add k 1) fun k' => ih k' t)) L,
      strictB (Nat.add k 1) fun k' => ih k' L)) n

@[expose] noncomputable def covC (n k : Nat) (L : List Nat) : Bool :=
  strictB (packL nW) fun NP => strictB (packL repW) fun UP => strictB (packL lamL) fun LP =>
    covR NP UP LP n k L

@[expose] noncomputable def covW : List Nat := cov0 ++ cov1 ++ cov2 ++ cov3 ++ cov4 ++ cov5 ++ cov6

@[expose] noncomputable def covK : Bool := covC 15625 0 covW

@[expose] noncomputable def repsOK : Bool :=
  bAnd(Nat.beq (lenK repW) 16, allL repW fun U => bAnd(canA U, unitK U))

@[expose] noncomputable def nChk (sA : Nat) : Bool :=
  bAnd(canA sA, bAnd(unitK sA, strictB (aToB sA) fun sB =>
    bAnd(isBlk sB, bAnd(Nat.beq (Nat.land (Nat.shiftRight sB 36) E) 1,
      strictB (cjB sB) fun C => strictB (trB C) fun sHB =>
        allL tBL fun tB => strictB (mulAB sA tB) fun W => strictB (bToA W) fun WA =>
          strictB (mulAB WA sHB) inT))))

@[expose] noncomputable def nOK : Bool := bAnd(Nat.beq (lenK nW) 48, allL nW nChk)

@[expose] noncomputable def lamOK : Bool :=
  bAnd(Nat.beq (lenK lamL) 6, allL lamL fun x =>
    bAnd(Nat.beq (Nat.land x (Nat.lor (Nat.shiftLeft 7 36) (Nat.shiftLeft 7 1060))) x,
      bAnd(Nat.blt (Nat.land (Nat.shiftRight x 36) 7) 5, bAnd(Nat.blt (Nat.shiftRight x 1060) 5,
        nrm1 (Nat.add (Nat.land (Nat.shiftRight x 36) 7) (Nat.mul 5 (Nat.shiftRight x 1060)))))))

@[expose] noncomputable def tChain (i : Nat) : Bool :=
  strictB (getK tBL (Nat.mul 2 i)) fun T =>
    bAnd(Nat.beq (getK tBL (Nat.add (Nat.mul 2 i) 1)) (strictN (bToA T) fun TA => mulAB TA SB),
      bIf(Nat.blt i 7, Nat.beq (getK tBL (Nat.add (Nat.mul 2 i) 2)) (mulAB RA T), true))

@[expose] noncomputable def tInvK (k : Nat) : Bool :=
  bAnd(canA (getK tinvL k), Nat.beq (mulAB (getK tinvL k) (getK tBL k)) DIAG)

@[expose] noncomputable def tSepK (j k : Nat) : Bool :=
  bIf(Nat.beq j k, true, strictB (mulAB (getK tinvL j) (getK tBL k)) fun c =>
    bIf(isScal c, false, true))

@[expose] noncomputable def comK (k GiA G : Nat) : Bool :=
  strictB (getK tBL k) fun T => strictB (bToA T) fun TA => strictB (mulAB TA G) fun W1 =>
    strictB (mulAB GiA W1) fun W2 => strictB (mulAB (getK tinvL k) W2) isScal

@[expose] noncomputable def t0K : Bool :=
  bAnd(Nat.beq (lenK tBL) 16, bAnd(Nat.beq (lenK tinvL) 16, bAnd(Nat.beq (getK tBL 0) DIAG,
    bAnd(allR tChain 8 0, bAnd(allR tInvK 16 0, bAnd(allR (fun j => allR (tSepK j) 16 0) 16 0,
      bAnd(Nat.beq R2A (bToA (getK tBL 4)),
        allR (fun k => bIf(bAnd(comK k (getK tinvL 2) (getK tBL 2),
          comK k (getK tinvL 1) (getK tBL 1)), bIf(Nat.beq k 0, true, Nat.beq k 8), true)) 16 0)))))))

@[expose] noncomputable def encA9 (c0 c1 c2 c3 c4 c5 c6 c7 c8 : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (ent (Nat.mod c0 5) (Nat.div c0 5) 0) (ent (Nat.mod c1 5) (Nat.div c1 5) 54))
    (Nat.add (ent (Nat.mod c2 5) (Nat.div c2 5) 108) (ent (Nat.mod c3 5) (Nat.div c3 5) 270)))
    (Nat.add (Nat.add (ent (Nat.mod c4 5) (Nat.div c4 5) 324) (ent (Nat.mod c5 5) (Nat.div c5 5) 378))
      (Nat.add (ent (Nat.mod c6 5) (Nat.div c6 5) 540)
        (Nat.add (ent (Nat.mod c7 5) (Nat.div c7 5) 594) (ent (Nat.mod c8 5) (Nat.div c8 5) 648))))

@[expose] noncomputable def constsOK : Bool :=
  let ln := fun (w s : Nat) => Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 w) 1) s
  let dbl := fun (x : Nat) => Nat.lor x (Nat.shiftLeft x 1024)
  bAnd(Nat.beq LOW (Nat.sub (Nat.shiftLeft 1 2048) 1),
  bAnd(Nat.beq RE (Nat.mul 255 (Nat.div (Nat.sub (Nat.shiftLeft 1 162) 1)
    (Nat.sub (Nat.shiftLeft 1 18) 1))),
  bAnd(Nat.beq LMd (dbl RE),
  bAnd(Nat.beq M0d (dbl (ln 54 108)), bAnd(Nat.beq M1d (dbl (ln 54 54)),
  bAnd(Nat.beq M2d (dbl (ln 54 0)),
  bAnd(Nat.beq BLKd (dbl (Nat.lor (Nat.lor (ln 8 144) (ln 8 90)) (Nat.lor (ln 8 0) (ln 8 18)))),
  bAnd(Nat.beq DIAG (Nat.lor (Nat.lor (Nat.shiftLeft 1 36) (Nat.shiftLeft 1 72)) (Nat.shiftLeft 1 108)),
  bAnd(Nat.beq E (dbl 255),
  bAnd(Nat.beq OA (dbl (encA9 1 1 1 1 1 1 1 1 1)), bAnd(Nat.beq LA (Nat.mul 255 OA),
  bAnd(Nat.beq RA (encA9 5 5 0 20 5 0 0 0 4), bAnd(Nat.beq SA (encA9 0 1 0 1 0 0 0 0 4),
    Nat.beq SB (aToB SA))))))))))))))

@[expose] noncomputable def u35PkCheck : Bool :=
  bAnd(constsOK, bAnd(repsOK, bAnd(nOK, bAnd(lamOK, bAnd(t0K, bAnd(covK, allL repW gu2K))))))

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by
  cases a <;> rfl

theorem allR_succ (f : Nat → Bool) (n lo : Nat) :
    allR f (n + 1) lo = (f lo && allR f n (lo + 1)) := by
  change bAnd(f lo, strictB (Nat.add lo 1) (allR f n)) = _
  rw [strictB_eq]
  cases f lo <;> rfl

theorem allR_add (f : Nat → Bool) (m : Nat) : ∀ (n lo : Nat), allR f m lo = true →
    allR f n (lo + m) = true → allR f (m + n) lo = true := by
  induction m with
  | zero => intro n lo _ h; simpa using h
  | succ m ih =>
    intro n lo h1 h2
    rw [Nat.add_right_comm, allR_succ]
    rw [allR_succ, Bool.and_eq_true] at h1
    have e : lo + 1 + m = lo + (m + 1) := by omega
    rw [Bool.and_eq_true]
    exact ⟨h1.1, ih n (lo + 1) h1.2 (by rw [e]; exact h2)⟩

theorem allR_chunks (f : Nat → Bool) (s : Nat) : ∀ (c lo : Nat),
    (∀ j < c, allR f s (lo + s * j) = true) → allR f (s * c) lo = true := by
  intro c
  induction c with
  | zero =>
    intro lo _
    rw [Nat.mul_zero]
    rfl
  | succ c ih =>
    intro lo h
    rw [Nat.mul_succ]
    exact allR_add f _ _ _ (ih lo fun j hj => h j (by omega)) (h c (by omega))

theorem gu2K_of (U : Nat) (h : ∀ j < 25, gu2R U (25 * j) 25 = true) : gu2K U = true := by
  have h' : ∀ j < 25, allR (gu2Step U) 25 (0 + 25 * j) = true := by
    intro j hj
    rw [Nat.zero_add]
    simpa only [gu2R, strictB_eq] using h j hj
  have := allR_chunks (gu2Step U) 25 25 0 h'
  simp only [gu2K, gu2R, strictB_eq]
  exact this

theorem allL_of_get (f : Nat → Bool) : ∀ (L : List Nat),
    (∀ i < lenK L, f (getK L i) = true) → allL L f = true
  | [], _ => rfl
  | x :: L, h => by
    change bAnd(f x, allL L f) = true
    have hx : f x = true := h 0 (Nat.succ_pos _)
    rw [hx]
    exact allL_of_get f L fun i hi => h (i + 1) (Nat.succ_lt_succ hi)

theorem covR_succ (NP UP LP m k : Nat) (L : List Nat) : covR NP UP LP (m + 1) k L =
    bIf(nrmV k, List.rec (motive := fun _ => Bool) false
        (fun e t _ => bAnd(entOK NP UP LP e k, covR NP UP LP m (k + 1) t)) L,
      covR NP UP LP m (k + 1) L) := by
  change bIf(nrmV k, List.rec (motive := fun _ => Bool) false
        (fun e t _ => bAnd(entOK NP UP LP e k, strictB (Nat.add k 1) fun k' => covR NP UP LP m k' t))
        L, strictB (Nat.add k 1) fun k' => covR NP UP LP m k' L) = _
  simp only [strictB_eq]

theorem covR_app (NP UP LP : Nat) (m : Nat) : ∀ (k : Nat) (L1 L2 : List Nat) (n : Nat),
    covR NP UP LP m k L1 = true → covR NP UP LP n (k + m) L2 = true →
      covR NP UP LP (m + n) k (L1 ++ L2) = true := by
  induction m with
  | zero =>
    intro k L1 L2 n h1 h2
    cases L1 with
    | nil => simpa using h2
    | cons e t => exact (Bool.false_ne_true h1).elim
  | succ m ih =>
    intro k L1 L2 n h1 h2
    have e : k + 1 + m = k + (m + 1) := by omega
    rw [Nat.add_right_comm, covR_succ]
    rw [covR_succ] at h1
    cases hv : nrmV k
    · rw [hv] at h1
      exact ih (k + 1) L1 L2 n h1 (by rw [e]; exact h2)
    · rw [hv] at h1
      cases L1 with
      | nil => exact (Bool.false_ne_true h1).elim
      | cons x t =>
        change bAnd(entOK NP UP LP x k, covR NP UP LP m (k + 1) t) = true at h1
        change bAnd(entOK NP UP LP x k, covR NP UP LP (m + n) (k + 1) (t ++ L2)) = true
        rw [bAnd_eq, Bool.and_eq_true] at h1 ⊢
        exact ⟨h1.1, ih (k + 1) t L2 n h1.2 (by rw [e]; exact h2)⟩

theorem covC_eq (n k : Nat) (L : List Nat) :
    covC n k L = covR (packL nW) (packL repW) (packL lamL) n k L := by
  simp only [covC, strictB_eq]

end U35Pk

end
