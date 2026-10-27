module

public import Certificates.Data.Kernel.Spor.EnumBase

public section

namespace CFSG.KS.HNT0

open CFSG.KC.Enum CFSG.KS.PEnum

@[expose] noncomputable def clK (n w m ng N : Nat) (G T POS : Nat → Nat) (k : Nat) : Bool :=
  strictB (T k) fun t => allN ng fun j =>
    strictB (r32 POS (Nat.add (Nat.mul k ng) j)) fun q =>
      bAnd(Nat.blt q N, Nat.beq (T q) (pcomp n w m (G j) t))

@[expose] noncomputable def failK : Nat := nat_lit 1048576

@[expose] noncomputable def dfE (DF : Nat → Nat) (p : Nat) : Nat :=
  fld(DF (Nat.shiftRight p (nat_lit 6)), Nat.mul (nat_lit 16) (Nat.land p (nat_lit 63)),
    nat_lit 65535)

@[expose] noncomputable def kidsK (M lo : Nat) : Nat :=
  strictN (Nat.land (Nat.land M (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1024)) (nat_lit 1)))
    (Nat.shiftRight M (nat_lit 1024))) fun X =>
    Nat.sub X (Nat.land X (Nat.sub (Nat.shiftLeft (nat_lit 1) lo) (nat_lit 1)))

@[expose] noncomputable def extK (Pc S k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.lor acc
    (Nat.shiftLeft fld(Pc, Nat.mul (nat_lit 10) fld(S, Nat.mul (nat_lit 10) i, nat_lit 1023),
      nat_lit 1023) (Nat.mul (nat_lit 10) i))) k

@[expose] noncomputable def andK (AL : Nat → Nat) (X k M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) M
    (fun i acc => Nat.land acc (AL fld(X, Nat.mul (nat_lit 10) i, nat_lit 1023))) k

@[expose] noncomputable def childK (AL PR : Nat → Nat) (S k M c : Nat) (f : Nat → Nat → Nat → Nat) :
    Nat :=
  strictN (PR c) fun Pc => strictN (extK Pc S k) fun X =>
  strictN (andK AL X k (Nat.land M (AL c))) fun M' =>
  strictN (Nat.lor c (Nat.lor (Nat.shiftLeft S (nat_lit 10))
    (Nat.shiftLeft X (Nat.mul (nat_lit 10) (Nat.succ k))))) fun S' =>
  f S' (Nat.succ (Nat.mul (nat_lit 2) k)) M'

@[expose] noncomputable def walkK (AL PR DF : Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat)
    (fun _ _ M lo p => nIf(Nat.beq (kidsK M lo) (nat_lit 0), p, failK))
    (fun d ih S k M lo p =>
      strictN (Nat.mul (nat_lit 1024) (Nat.sub (nat_lit 5) d)) fun base =>
      Nat.rec (motive := fun _ => Nat → Nat → Nat)
        (fun K p => nIf(Nat.beq K (nat_lit 0), p, failK))
        (fun _ loop K p => nIf(Nat.beq K (nat_lit 0), p,
          strictN (dfE DF p) fun e => strictN (Nat.sub e base) fun c =>
          strictN (Nat.shiftLeft (nat_lit 1) c) fun b =>
          nIf(bAnd(Nat.ble base e, bAnd(Nat.blt (nat_lit 0) (Nat.land K b),
              Nat.beq (Nat.land K (Nat.sub b (nat_lit 1))) (nat_lit 0))),
            strictN (childK AL PR S k M c fun S' k' M' => ih S' k' M' (Nat.succ c) (Nat.succ p))
              fun p' => loop (Nat.sub K b) p',
            failK)))
        (nat_lit 1024) (kidsK M lo) p)

@[expose] noncomputable def rootK (AL DF DFO : Nat → Nat) (z n : Nat) : Bool :=
  Nat.beq (kidsK (AL z) (nat_lit 0))
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc => strictN (dfE DF (DFO j)) fun e =>
      Nat.lor acc (nIf(bAnd(Nat.ble (nat_lit 1024) e, Nat.blt e (nat_lit 2048)),
        Nat.shiftLeft (nat_lit 1) (Nat.sub e (nat_lit 1024)),
        Nat.shiftLeft (nat_lit 1) (nat_lit 2048)))) n)

@[expose] noncomputable def subK (AL PR DF DFO : Nat → Nat) (z j : Nat) : Bool :=
  strictB (DFO j) fun p => strictB (Nat.sub (dfE DF p) (nat_lit 1024)) fun c =>
  strictB (DFO (Nat.succ j)) fun q => bAnd(Nat.blt q failK,
    Nat.beq (childK AL PR z (nat_lit 1) (AL z) c fun S k M =>
      walkK AL PR DF (nat_lit 4) S k M (Nat.succ c) (Nat.succ p)) q)

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def bitsK (S k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.lor acc
    (Nat.shiftLeft (nat_lit 1) fld(S, Nat.mul (nat_lit 10) i, nat_lit 1023))) k

@[expose] noncomputable def basisK (AL PR : Nat → Nat) (bs : List Nat) :
    Nat → Nat → Nat → Nat → (Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → (Nat → Nat → Bool) → Bool)
    (fun S k _ _ f => f S k)
    (fun c _ ih S k SB AA f => bAnd(Nat.beq fld(SB, c, nat_lit 1) (nat_lit 0),
      bAnd(Nat.beq fld(AA, c, nat_lit 1) (nat_lit 1),
      strictB (PR c) fun Pc => strictB (extK Pc S k) fun X =>
      strictB (Nat.lor c (Nat.lor (Nat.shiftLeft S (nat_lit 10))
        (Nat.shiftLeft X (Nat.mul (nat_lit 10) (Nat.succ k))))) fun S' =>
      strictB (Nat.succ (Nat.mul (nat_lit 2) k)) fun k' =>
      strictB (bitsK S' k') fun SB' =>
      strictB (andK AL S' k' (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1024)) (nat_lit 1)))
        fun AA' => ih S' k' SB' AA' f))) bs

@[expose] noncomputable def wmK (AL : Nat → Nat) (S k W : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) W (fun i acc => strictN fld(S, Nat.mul (nat_lit 10) i, nat_lit 1023)
    fun s => Nat.land acc (Nat.lor (AL s) (Nat.shiftLeft (nat_lit 1) s))) k

@[expose] noncomputable def maskL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) x) ih) l

@[expose] noncomputable def ebK (AL PR : Nat → Nat) (m z : Nat) (EB : List (List Nat))
    (ZW : List Nat) : Bool :=
  bAnd(Nat.beq (lenK EB) (nat_lit 3), bAnd(Nat.beq (lenK ZW) (nat_lit 3),
    strictB (maskL ZW) fun zm =>
    List.rec (motive := fun _ => Nat → Bool) (fun W => Nat.beq (Nat.land W zm) W)
      (fun bs _ ih W => bAnd(Nat.beq (lenK bs) (nat_lit 5),
        basisK AL PR bs z (nat_lit 1) (Nat.shiftLeft (nat_lit 1) z)
          (Nat.land (AL z) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1024)) (nat_lit 1)))
          fun S k => strictB (wmK AL S k W) ih))
      EB (Nat.sub (Nat.shiftLeft (nat_lit 1) m) (nat_lit 1))))

end CFSG.KS.HNT0

end
