module

public import Certificates.Data.Kernel.SmithEKS
public import Certificates.Data.SMod20BasicC8

public section

namespace CFSG.SmithE.K

open CFSG.SmithE

@[expose] noncomputable def c8ap (A : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0) (fun c _ ih x => c * (x % 2) ^^^ ih (x / 2))
    A x

@[expose] noncomputable def c8comm (A B : List Nat) : Bool :=
  (List.range 20).all fun m => c8ap A (B.getD m 0) == c8ap B (A.getD m 0)

@[expose] noncomputable def c8Q (C : List (List Nat)) : List (List Nat) := c8Pts.toList.map fun r => C.getD r []

@[expose] noncomputable def c8R (Q : List (List Nat)) : List (Nat × List Nat) := c8Pts.toList.zip Q

@[expose] noncomputable def c8PtsK (A B : List Nat) (Q : List (List Nat)) : Bool :=
  c8Pts.size == 45 && c8Pts.toList.all (fun r => decide (r < 693)) &&
    Q.all fun T => c8comm T A && c8comm T B

@[expose] noncomputable def c8FixK (A B : List Nat) : Bool :=
  (List.range 8).all (fun m => c8ap A (2 ^ m) == 2 ^ m && c8ap B (2 ^ m) == 2 ^ m) &&
    (List.range 4096).all fun j =>
      (c8ap A (256 * j) == 256 * j && c8ap B (256 * j) == 256 * j) == (j == 0)

@[expose] noncomputable def c8RestrB (A B : List Nat) (R : List (Nat × List Nat)) (s : Nat) (T : List Nat) :
    Bool :=
  !(c8comm T A && c8comm T B) || R.all fun rq =>
    !((List.range 8).all fun b => T.getD b 0 == rq.2.getD b 0) || s == rq.1

@[expose] noncomputable def c8RestrK (A B : List Nat) (R : List (Nat × List Nat)) :
    List (List Nat) → Nat → Bool
  | [], _ => true
  | T :: l, s => c8RestrB A B R s T && c8RestrK A B R l (s + 1)

@[expose] noncomputable def c8StepK (A : List Nat) (Q : List (List Nat)) (s x : Nat) : Nat :=
  let y := c8ap (Q.getD (s / 2) A) x
  if s % 2 == 1 then y ^^^ x else y

@[expose] noncomputable def c8PathK (A : List Nat) (Q : List (List Nat)) (p : List Nat) (x : Nat) : Nat :=
  p.foldl (fun x s => c8StepK A Q s x) x

@[expose] noncomputable def c8IrrK (A : List Nat) (Q : List (List Nat)) : Bool :=
  decide (c8Root < 256) && c8Root != 0 && c8Back.size == 256 && c8Fwd.size == 8 &&
    (List.range 256).all (fun d => d == 0 ||
      ((c8Back[d]!).all (fun s => decide (s < 90)) && c8PathK A Q c8Back[d]! d == c8Root)) &&
    (List.range 8).all fun b =>
      (c8Fwd[b]!).1.all (fun s => decide (s < 90)) &&
        (c8Fwd[b]!).2.all (fun s => decide (s < 90)) &&
        (c8PathK A Q (c8Fwd[b]!).1 c8Root ^^^ c8PathK A Q (c8Fwd[b]!).2 c8Root) == 2 ^ b

@[expose] noncomputable def c8RigK (A : List Nat) (S : List (List Nat)) : Bool :=
  let w := c8ap A rigE0 ^^^ rigE0
  (List.range 4096).all fun j => let v := c8ap A (256 * j) ^^^ 256 * j
    !(S.all fun T => c8ap T v == v) || v == 0 || v == w

@[expose] noncomputable def c8Word (C : List (List Nat)) (u : List Nat) (x : Nat) : Nat :=
  u.foldl (fun x r => c8ap (C.getD r []) x) x

@[expose] noncomputable def c8Rig2K (A : List Nat) (C : List (List Nat)) : Bool :=
  let w := c8ap A rigE0 ^^^ rigE0
  w != 0 && rigS.all (fun s => c8Pts.toList.contains s && c8ap (C.getD s []) w == w) &&
    rigWords.size == 12 && rigCoef.size == 20 &&
    rigWords.toList.all (fun u => u.all fun r => c8Pts.toList.contains r || r == 0 || r == 1) &&
    (List.range 20).all fun m =>
      c8ap (rigWords.toList.map (fun u => c8Word C u w) ++ [1, 2, 4, 8, 16, 32, 64, 128])
        (rigCoef.toList.getD m 0) == 2 ^ m

end CFSG.SmithE.K
