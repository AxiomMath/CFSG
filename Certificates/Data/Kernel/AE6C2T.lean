module

public import Certificates.Data.Kernel.AE6C2B

public section

namespace CFSG.KC.AE6C2

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F
open CFSG.KC.Census (strictLA strictNA)

@[expose] noncomputable def lvlT (T : List Nat) (k : Nat → List Nat → List Nat) :
    Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ acc => acc)
    (fun t _ ih h acc => strictNA (CFSG.KC.KGC31P.pc 360 9 h t) fun x => ih h (k x acc)) T

@[expose] noncomputable def prod4 (T0 T1 T2 T3 : List Nat) (h : Nat) : List Nat :=
  lvlT T0 (lvlT T1 (lvlT T2 (lvlT T3 List.cons))) h []

@[expose] noncomputable def zfilt (mem : Nat → Bool) (L : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun x _ ih C => List.rec (motive := fun _ => List Nat) []
      (fun c C' _ => Bool.rec (ih C') (x :: ih C') (mem c)) C) L

@[expose] noncomputable def qsAllT (mem : Nat → Bool) (PL T0 T1 T2 T3 G : List Nat) :
    List (List Nat) :=
  (List.range 8).map fun i => strictNA (G.getD i (pidn 360 9)) fun g =>
    strictNA (invN 360 9 g) fun gi =>
      strictLA (T3.map fun t => CFSG.KC.KGC31P.pc 360 9 t gi) fun T3' =>
        zfilt mem PL (prod4 T0 T1 T2 T3' g)

@[expose] noncomputable def rngN (x : Nat) : Bool := allN 360 fun i => Nat.blt (pg 9 (mask 9) x i) 360

@[expose] noncomputable def rngG (G : List Nat) : Bool :=
  (List.range 8).all fun i => rngN (invN 360 9 (G.getD i (pidn 360 9)))

@[expose] noncomputable def basicT (G P T0 T1 T2 T3 L3I B : List Nat) (CZ : List (List Nat)) : Bool :=
  strictLA P fun P => strictLA G fun G => strictLLA CZ fun CZ =>
  strictLA T0 fun T0 => strictLA T1 fun T1 => strictLA T2 fun T2 => strictLA T3 fun T3 =>
  strictB M5 fun M => strictB (buildT keyP M P) fun T =>
  strictB (buildB 3240 M P) fun BP => strictB P.length fun n =>
  Bool.rec false
    (strictLLA (qsAllT (memK keyP 3240 M T BP n) P T0 T1 T2 T3 G) fun Qs =>
      strictLA (Qs.getD 3 []) fun Q3 =>
      strictLLA (lsRec P L3I) fun Ls => strictLA (l3N Q3 B CZ) fun L3 =>
      strictLA (L3.filter (commAllN P)) fun A =>
      Qs == [P, P, P, Q3, P, P, P, P] && c2BasicN G P Qs Ls &&
        [A, A, A, L3.filter (commAllN Q3), A, A, A, A] == Ls)
    (tblOK keyP 3240 M T BP P && rngG G)

end CFSG.KC.AE6C2

end
