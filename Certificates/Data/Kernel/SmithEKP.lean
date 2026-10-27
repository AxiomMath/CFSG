module

public import Certificates.Data.CFSGNative.F4.Unitary

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native

@[expose] def l20 : Nat := (2 ^ 400 - 1) / (2 ^ 20 - 1)

@[expose] noncomputable def pkW (w : Nat) : List Nat → Nat :=
  fun L => List.rec (motive := fun _ => Nat) 0 (fun x _ ih => x + (ih <<< w)) L

@[expose] noncomputable def lmulP (ONE : Nat) : List Nat → Nat → Nat :=
  fun A => List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih Z => ((Z &&& ONE) * a) ^^^ ih (Z >>> 1)) A

@[expose] noncomputable def bmulP (ONE : Nat) : List Nat → Nat → Nat :=
  fun Qs => List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun q _ ih Z => (q &&& ((Z &&& ONE) * (2 ^ 20 - 1))) ^^^ ih (Z >>> 1)) Qs

@[expose] noncomputable def qsOf (C : List (List Nat)) : List Nat :=
  (List.range 20).map fun j => pkW 400 (C.map fun c => c.getD j 0 * l20)

@[expose] noncomputable def planesP (P : List Nat) : List Nat :=
  (List.range 12).map fun b => pkW 400 (P.map fun q => (q >>> b) % 2)

@[expose] noncomputable def selX : List Nat → Nat → Nat :=
  fun Pl => List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih s => (if s % 2 == 1 then x else 0) ^^^ ih (s / 2)) Pl

@[expose] noncomputable def hM (p i : Nat) : Nat :=
  (List.range 12).foldr (fun b acc => (hermC p (2 ^ b) >>> i) % 2 + 2 * acc) 0

@[expose] noncomputable def orthF (REP : Nat) (Pl : List Nat) (p : Nat) : Nat :=
  ((REP ^^^ (selX Pl (hM p 0) ||| selX Pl (hM p 1))) &&& REP) * (2 ^ 400 - 1)

@[expose] noncomputable def rowF (ONE REP DATA Bpk : Nat) (Qs Pl : List Nat) (p : Nat)
    (A : List Nat) (Ap : Nat) : Bool :=
  let X := lmulP ONE A Bpk
  let Y := bmulP ONE Qs (REP * Ap)
  let O := orthF REP Pl p
  ((X ^^^ Y) &&& O) == 0 && ((lmulP ONE A Y ^^^ bmulP ONE Qs X) &&& (DATA ^^^ O)) == 0

@[expose] noncomputable def rowsF (ONE REP DATA Bpk : Nat) (Qs Pl : List Nat) :
    List Nat → List (List Nat) → List Nat → Bool :=
  fun R => List.rec (motive := fun _ => List (List Nat) → List Nat → Bool) (fun _ _ => true)
    (fun p _ ih Cr Pr => rowF ONE REP DATA Bpk Qs Pl p (Cr.headD []) (Pr.headD 0) &&
      ih Cr.tail Pr.tail) R

@[expose] noncomputable def chkPF (P : List Nat) (C : List (List Nat)) : Bool :=
  let REP := pkW 400 (List.replicate 693 1)
  let Q := C.map (pkW 20)
  P.length == 693 && C.length == 693 && P.all (fun p => decide (p < 4096)) &&
    C.all (fun c => c.length == 20 && c.all fun x => decide (x < 2 ^ 20)) &&
    rowsF (REP * l20) REP (REP * (2 ^ 400 - 1)) (pkW 400 Q) (qsOf C) (planesP P) P C Q

end CFSG.SmithE.K
