module

public import Certificates.Data.Kernel.AE6C2N
public import Certificates.Data.Kernel.Census.PackedL

public section

namespace CFSG.KC.AE6C2

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F
open CFSG.KC.Census (strictLA strictNA)

@[expose] noncomputable def strictLLA {β : Sort _} (L : List (List Nat)) (k : List (List Nat) → β) :
    β :=
  List.rec (motive := fun _ => (List (List Nat) → β) → β) (fun k => k [])
    (fun l _ ih k => strictLA l fun l' => ih fun t => k (l' :: t)) L k

@[expose] noncomputable def keyM (p M y : Nat) : Nat := Nat.mod (Nat.mod y M) p

@[expose] noncomputable def lane9 (T i : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul i (nat_lit 9))) (nat_lit 511)

@[expose] noncomputable def laneM (s M B j : Nat) : Nat := Nat.mod (Nat.shiftRight B (Nat.mul j s)) M

@[expose] noncomputable def buildT (p M : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun x _ ih i acc => strictN (Nat.succ i) fun i' =>
      strictN (Nat.lor acc (Nat.shiftLeft i (Nat.mul (keyM p M x) (nat_lit 9)))) fun a => ih i' a)
    L (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def buildB (s M : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun x _ ih i acc => strictN (Nat.succ i) fun i' =>
      strictN (Nat.lor acc (Nat.shiftLeft (Nat.mod x M) (Nat.mul i s))) fun a => ih i' a)
    L (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def tblAux (p s M T B : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => Bool.rec false
      (Bool.rec false (strictB (Nat.succ i) ih) (Nat.beq (laneM s M B i) (Nat.mod x M)))
      (Nat.beq (lane9 T (keyM p M x)) i)) L

@[expose] noncomputable def tblOK (p s M T B : Nat) (L : List Nat) : Bool := tblAux p s M T B L 0

@[expose] noncomputable def memK (p s M T B n y : Nat) : Bool :=
  (fun j => Bool.rec false (Nat.beq (laneM s M B j) (Nat.mod y M)) (Nat.blt j n))
    (lane9 T (keyM p M y))

@[expose] noncomputable def qsAllK (mem : Nat → Bool) (PL G : List Nat) : List (List Nat) :=
  (List.range 8).map fun i => strictNA (G.getD i (pidn 360 9)) fun g =>
    strictNA (invN 360 9 g) fun gi => PL.filter fun x => mem (conjN g gi x)

@[expose] noncomputable def lsRec (P L3I : List Nat) : List (List Nat) :=
  let A := [P.getD 335 0, P.getD 511 0]
  [A, A, A, L3I.map fun k => P.getD k 0, A, A, A, A]

@[expose] def keyP : Nat := 196613

@[expose] noncomputable def M5 : Nat := 2 ^ (360 * 9)

@[expose] noncomputable def basicF (G P L3I B : List Nat) (CZ : List (List Nat)) : Bool :=
  strictLA P fun P => strictLA G fun G => strictLLA CZ fun CZ =>
  strictB M5 fun M => strictB (buildT keyP M P) fun T =>
  strictB (buildB 3240 M P) fun BP => strictB P.length fun n =>
  Bool.rec false
    (strictLLA (qsAllK (memK keyP 3240 M T BP n) P G) fun Qs => strictLA (Qs.getD 3 []) fun Q3 =>
      strictLLA (lsRec P L3I) fun Ls => strictLA (l3N Q3 B CZ) fun L3 =>
      strictLA (L3.filter (commAllN P)) fun A =>
      Qs == [P, P, P, Q3, P, P, P, P] && c2BasicN G P Qs Ls &&
        [A, A, A, L3.filter (commAllN Q3), A, A, A, A] == Ls)
    (tblOK keyP 3240 M T BP P)

end CFSG.KC.AE6C2

end
