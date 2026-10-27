module

public import Certificates.Data.Kernel.SmithEKM
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.SmithE.K

@[expose] noncomputable def bitsOf (b : Nat) : List Nat → Nat :=
  fun L => List.rec (motive := fun _ => Nat) 0 (fun x _ ih => (x >>> b) % 2 + 2 * ih) L

@[expose] noncomputable def planesOf (L : List Nat) : List Nat :=
  (List.range 20).map fun b => bitsOf b L

@[expose] noncomputable def formRow (u : Nat) : List Nat → Nat → Nat :=
  fun Bs => List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun B _ ih b => (bif u.testBit (b ^^^ 1) then B else 0) ^^^ ih (b + 1)) Bs

@[expose] noncomputable def planesK (P : List Nat) (M : Nat) : Bool :=
  P.all (fun x => cntK 693 x == 21) && CFSG.Decide.bitsetNodup (P.map (· % M))

@[expose] noncomputable def oppRowK (Pi : Nat) : List Nat → Nat → Bool :=
  fun P => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun Pj _ ih R => ((R % 2 == 1) == (Pi &&& Pj == 0)) && ih (R >>> 1)) P

@[expose] noncomputable def gramChunkK (W P : List Nat) (s n : Nat) : Bool :=
  let Bs := planesOf W
  (List.range' s n).all fun i => oppRowK (P.getD i 0) P (formRow (W.getD i 0) Bs 0)

@[expose] noncomputable def formColsK (Bs : List Nat) : List Nat → List Nat → Bool :=
  fun T => List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun t _ ih E => (formRow t Bs 0 == E.headD 0) && ih E.tail) T

@[expose] def idCols : List Nat := (List.range 20).map (2 ^ ·)

@[expose] noncomputable def formInvK (C : List (List Nat)) : Bool :=
  let E := idCols.map fun t => formRow t (planesOf idCols) 0
  C.all fun T => formColsK (planesOf T) T E

end CFSG.SmithE.K
