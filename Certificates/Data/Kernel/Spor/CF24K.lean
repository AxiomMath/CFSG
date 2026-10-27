module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.CF24

@[expose] noncomputable def zc (c : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.negSucc (Nat.shiftRight c 1))
    (Int.ofNat (Nat.succ (Nat.shiftRight c 1))) (Nat.beq (Nat.land c 1) 0)

@[expose] noncomputable def codesZ (cs : List Nat) : List Int :=
  List.rec (motive := fun _ => List Int) List.nil (fun c _ ih => List.cons (zc c) ih) cs

@[expose] noncomputable def nthW (L : List (List Int)) : Nat → List Int :=
  List.rec (motive := fun _ => Nat → List Int) (fun _ => List.nil)
    (fun w _ ih k => Nat.rec (motive := fun _ => List Int) w (fun k' _ => ih k') k) L

@[expose] noncomputable def sel7 (a0 a1 a2 a3 a4 a5 a6 h : Nat) : Nat :=
  nIf(Nat.beq h 0, a0, nIf(Nat.beq h 1, a1, nIf(Nat.beq h 2, a2, nIf(Nat.beq h 3, a3,
    nIf(Nat.beq h 4, a4, nIf(Nat.beq h 5, a5, a6))))))

@[expose] noncomputable def sel5 (a0 a1 a2 a3 a4 h : Nat) : Nat :=
  nIf(Nat.beq h 0, a0, nIf(Nat.beq h 1, a1, nIf(Nat.beq h 2, a2, nIf(Nat.beq h 3, a3, a4))))

@[expose] noncomputable def maskL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor (Nat.shiftLeft 1 x) ih) L

end CFSG.KS.CF24

end
