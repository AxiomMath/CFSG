module

public import CFSG.Certificates.Kernel.MonsterConv.PermValid
public import CFSG.Sporadic.Recognition.LyonsFinalFamilyInputs
public import CFSG.Sporadic.Recognition.LyonsFinalBInputs

public section

namespace CFSG.KC.LyBenes

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] noncomputable def planesId (k : Nat) (Ns : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun b ih => andB ih (Nat.beq (netsApply k (Nat.shiftLeft 1 k) 1 Ns
      (idPlane (Nat.shiftLeft 1 k) b)) (idPlane (Nat.shiftLeft 1 k) b))) k

@[expose] noncomputable def planesEq (k : Nat) (Ns : List Nat) (N : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun b ih => andB ih (Nat.beq (netsApply k (Nat.shiftLeft 1 k) 1 Ns
      (idPlane (Nat.shiftLeft 1 k) b)) (netApply k (Nat.shiftLeft 1 k) 1 N
        (idPlane (Nat.shiftLeft 1 k) b)))) k

@[expose] noncomputable def rawOf (T : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.lor acc (Nat.shiftLeft (Nat.land (T j) (ones 75735)) (Nat.mul j 75735))) 15

@[expose] noncomputable def tabPlane (RAW b : Nat) : Nat :=
  Nat.lor (Nat.land (rawPlane RAW 17 131072 17 0 b) (ones 66825))
    (Nat.land (idPlane 131072 b) (Nat.xor (ones 131072) (ones 66825)))

@[expose] noncomputable def tabPlanes (T : Nat → Nat) : Nat :=
  strictN (rawOf T) fun RAW => Nat.rec (motive := fun _ => Nat) 0
    (fun b acc => Nat.lor acc (Nat.shiftLeft (tabPlane RAW b) (Nat.mul b 131072))) 17

@[expose] noncomputable def bindOK (T : Nat → Nat) (N : Nat) : Bool :=
  andB (netValid 17 N)
    (Nat.beq (netApply 17 131072 (repU 131072 17) N (idP 17)) (tabPlanes T))

@[expose] noncomputable def letIdx (l : Fin 6 × Bool) : Nat :=
  nIf(Nat.beq l.1.val 0, 0, nIf(Nat.beq l.1.val 1, Bool.rec 2 1 l.2, Nat.add l.1.val 1))

@[expose] noncomputable def zIdx (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun m => nIf(Nat.beq m 1, 0, 1))
    (fun m => nIf(Nat.beq m 0, 0, 2)) z

@[expose] noncomputable def genNets (NS : Nat → Nat) (w : List Int) : List Nat :=
  w.map fun z => NS (zIdx z)

@[expose] noncomputable def wordNets (NS : Nat → Nat) (r : List (Fin 6 × Bool)) : List Nat :=
  r.map fun l => NS (letIdx l)

@[expose] noncomputable def kitBindOK (NS CT DT : Nat → Nat) : Bool :=
  andB (bindOK CT (NS 0)) (bindOK DT (NS 1))

@[expose] noncomputable def kitValidOK (NS : Nat → Nat) : Bool :=
  andB (andB (netValid 17 (NS 2)) (netValid 17 (NS 3)))
    (andB (netValid 17 (NS 4)) (netValid 17 (NS 5)))

@[expose] noncomputable def kitInvOK (NS : Nat → Nat) : Bool :=
  andB (andB (planesId 17 [NS 0, NS 0]) (planesId 17 [NS 2, NS 1]))
    (andB (planesId 17 [NS 3, NS 3]) (andB (planesId 17 [NS 4, NS 4]) (planesId 17 [NS 5, NS 5])))

@[expose] noncomputable def kitGenOK (NS : Nat → Nat) : Bool :=
  andB (planesEq 17 (genNets NS (genZ 2)) (NS 3))
    (andB (planesEq 17 (genNets NS (genZ 3)) (NS 4)) (planesEq 17 (genNets NS (genZ 4)) (NS 5)))

@[expose] noncomputable def bNetOK (NS : Nat → Nat) (r : List (Fin 6 × Bool)) : Bool :=
  andB (isBWord r) (planesId 17 (wordNets NS r))

end CFSG.KC.LyBenes

end
