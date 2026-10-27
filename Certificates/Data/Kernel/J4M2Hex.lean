module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2PermData
public import Certificates.Data.Kernel.LocalQT.Lat7
public import CFSG.Certificates.Kernel.Spor.PK.Enc
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.J4M2K

open CFSG.KC.Enum CFSG.KC.LQT.L CFSG.KS.PK CFSG.Quasithin.J4M2
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

@[expose] noncomputable def allR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(f k, ih)) n

@[expose] noncomputable def anyR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k ih => bIf(f k, true, ih)) n

@[expose] noncomputable def firstR (p : Nat → Bool) (d m i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun _ ih j => nIf(p j, j, ih (Nat.succ j))) m i

@[expose] noncomputable def maskL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) x) ih) l

@[expose] noncomputable def hexP : Nat := pmk (nat_lit 77) (nat_lit 22) fun i => maskL (hexLab.getD i [])

@[expose] noncomputable def gimg (g : Equiv.Perm (Fin 22)) : Nat :=
  pmk (nat_lit 22) (nat_lit 5) fun p => (g (Fin.ofNat 22 p)).val

@[expose] noncomputable def imgR (f : Nat → Nat) (m n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p ih => nIf(Nat.testBit m p, Nat.lor (Nat.shiftLeft (nat_lit 1) (f p)) ih, ih)) n

@[expose] noncomputable def imgM (f : Nat → Nat) (m : Nat) : Nat := imgR f m (nat_lit 22)

@[expose] noncomputable def distK (H : Nat) : Bool :=
  allR (nat_lit 77) fun i => allR (nat_lit 77) fun j =>
    bIf(Nat.beq i j, true, bIf(Nat.beq (fd (nat_lit 22) H i) (fd (nat_lit 22) H j), false, true))

@[expose] noncomputable def permK (H : Nat) (f : Nat → Nat) : Bool :=
  allR (nat_lit 77) fun i => strictB (imgM f (fd (nat_lit 22) H i)) fun t =>
    anyR (nat_lit 77) fun j => Nat.beq t (fd (nat_lit 22) H j)

@[expose] noncomputable def phiK (H : Nat) (f : Nat → Nat) (i : Nat) : Nat :=
  strictN (imgM f (fd (nat_lit 22) H i)) fun t =>
    firstR (fun j => Nat.beq (fd (nat_lit 22) H j) t) i (nat_lit 77) (nat_lit 0)

@[expose] noncomputable def phiC (H G : Nat) : Nat :=
  pmk (nat_lit 77) (nat_lit 7) (phiK H (fd (nat_lit 5) G))

@[expose] noncomputable def sigC (n : Nat) : Nat :=
  pmk (nat_lit 77) (nat_lit 7) fun i => (sigData.getD n []).getD i 0

@[expose] noncomputable def ev7 (gs : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (one7 (nat_lit 77))
    (fun i _ ih => mul7 (nat_lit 77) (gs.getD i (one7 (nat_lit 77))) ih) w

@[expose] noncomputable def wordsCore (A B : Nat) (O : List Nat) : Bool :=
  bAnd(bIf(Nat.beq A (one7 (nat_lit 77)), false, true), bAnd(Nat.beq A (ev7 O wordPhiA),
    bAnd(Nat.beq B (ev7 O wordPhiB),
      allR (nat_lit 5) fun k => Nat.beq (O.getD k 0) (ev7 [A, B] (wordsOdd.getD k [])))))

@[expose] noncomputable def tCore (S : SetK) (TG P0 PH : List Nat) : Bool :=
  bAnd(closedK7 (nat_lit 77) TG S, bAnd(Nat.beq S.size (nat_lit 256),
    bAnd(allA P0 fun x => memT S.t x, allA PH fun x => memT S.t x)))

@[expose] noncomputable def fixK (f : Nat → Nat) : Bool := Nat.beq (f (nat_lit 0)) (nat_lit 0)

@[expose] noncomputable def presK (f : Nat → Nat) : Bool :=
  allA i5List fun i => anyA i5List fun j => Nat.beq (f i) j

@[expose] noncomputable def distChk : Bool := strictB hexP distK

@[expose] noncomputable def hexGenK (k : Nat) : Bool :=
  strictB hexP fun H => strictB (gimg (blockGens.getD k 1)) fun G => permK H (fd (nat_lit 5) G)

@[expose] noncomputable def wordsChk : Bool :=
  strictB hexP fun H => strictB (phiC H (gimg (mGens.getD 0 1))) fun A =>
    strictB (phiC H (gimg (mGens.getD 1 1))) fun B =>
      strictB (sigC (nat_lit 12)) fun o0 => strictB (sigC (nat_lit 13)) fun o1 =>
        strictB (sigC (nat_lit 14)) fun o2 => strictB (sigC (nat_lit 15)) fun o3 =>
          strictB (sigC (nat_lit 16)) fun o4 => wordsCore A B [o0, o1, o2, o3, o4]

@[expose] noncomputable def tChk : Bool :=
  strictB (sigC (nat_lit 28)) fun a => strictB (sigC (nat_lit 29)) fun b =>
    strictB (sigC (nat_lit 30)) fun c => strictB (sigC (nat_lit 17)) fun d =>
      strictB hexP fun H =>
        tCore (bfsK7 (nat_lit 77) [a, b, c, d] (nat_lit 64)) [a, b, c, d]
          ((List.range 15).map fun j => sigC (17 + j)) (tGens.map fun g => phiC H (gimg g))

@[expose] noncomputable def classK (j : Nat) : Bool :=
  bIf(Nat.beq j (nat_lit 4), true, strictB hexP fun H =>
    bIf(allA (members.getD j []) fun g => strictB (gimg g) fun G => fixK (phiK H (fd (nat_lit 5) G)),
      true,
      allA (members.getD j []) fun g => strictB (gimg g) fun G => presK (phiK H (fd (nat_lit 5) G))))

@[expose] noncomputable def p0Chk : Bool :=
  allR (nat_lit 15) fun j => bAnd(fixK fun i => (sigData.getD (17 + j) []).getD i 0,
    presK fun i => (sigData.getD (17 + j) []).getD i 0)

end CFSG.KC.J4M2K

end
