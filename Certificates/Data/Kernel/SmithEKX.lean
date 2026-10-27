module

public import Certificates.Data.Kernel.SmithEKM
public import Certificates.Data.Kernel.SmithEKN

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73

@[expose] noncomputable def ixComm (s t : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => Nat.beq (at' 5 s (at' 5 t (Nat.sub 20 k))) (at' 5 t (at' 5 s (Nat.sub 20 k))) &&
      acc) 21

@[expose] noncomputable def ixBit (c r : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight c r) 1) 1

@[expose] noncomputable def ixPlane (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun a acc => Nat.lor acc (bif ixBit a j then Nat.shiftLeft 1 a else 0)) 512

@[expose] noncomputable def ixOut (CP s r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.xor acc (bif ixBit (at' 9 CP (at' 5 s j)) r then ixPlane j else 0)) 9

@[expose] noncomputable def ixFix (CP s : Nat) : Nat :=
  Nat.xor (Nat.sub (Nat.shiftLeft 1 512) 1)
    (Nat.rec (motive := fun _ => Nat) 0
      (fun r acc => Nat.lor acc (Nat.xor (ixPlane r) (ixOut CP s r))) 9)

@[expose] noncomputable def ixS (e : Nat) : Nat := Nat.land e (Nat.sub (Nat.shiftLeft 1 105) 1)

@[expose] noncomputable def ixF (e : Nat) : Nat :=
  Nat.land (Nat.shiftRight e 105) (Nat.sub (Nat.shiftLeft 1 512) 1)

@[expose] noncomputable def ixC (e : Nat) : Nat := Nat.shiftRight e 617

@[expose] noncomputable def ixRow (i e : Nat) (D : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun d _ ih j =>
      (bif ixComm (ixS e) (ixS d) then
          ixBit (ixC e) j && (Nat.beq i j ||
            (Nat.ble (cntK 17 (Nat.land (ixF e) (ixF d))) 16 &&
              Nat.ble (cntK 28 (Nat.land (ixC e) (ixC d))) 27))
        else !ixBit (ixC e) j) && ih (Nat.succ j)) D 0

@[expose] noncomputable def ixGet (D : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) k) D

@[expose] noncomputable def ixChunk (CP : Nat) (D : List Nat) (a n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => acc && (let e := ixGet D (Nat.add a k)
      Nat.beq (ixF e) (ixFix CP (ixS e)) && Nat.ble (cntK 65 (ixF e)) 64 &&
        ixRow (Nat.add a k) e D)) n

@[expose] noncomputable def ixSs (D : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e _ ih => ixS e :: ih) D

@[expose] noncomputable def ixFlat (R : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun r _ ih => r ++ ih) R

@[expose] noncomputable def ixEq : List Nat → List Nat → Bool :=
  fun L => List.rec (motive := fun _ => List Nat → Bool) (fun M => List.rec true (fun _ _ _ => false) M)
    (fun x _ ih M => List.rec (motive := fun _ => Bool) false (fun y M' _ => Nat.beq x y && ih M') M) L

@[expose] noncomputable def ixPin (R : List (List Nat)) (D : List Nat) : Bool :=
  ixEq (ixSs D) (ixFlat R)

@[expose] noncomputable def ixAll (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k) n

@[expose] noncomputable def ixCo (CP : Nat) : Bool :=
  ixAll 21 (fun k => Nat.blt 0 (at' 9 CP k) && Nat.blt (at' 9 CP k) 512) &&
    ixAll 21 (fun k => ixAll 21 fun l => Nat.beq k l || !Nat.beq (at' 9 CP k) (at' 9 CP l)) &&
    ixAll 21 (fun k => ixAll 21 fun l => !Nat.blt k l ||
      (ixAll 21 (fun m => !Nat.beq (at' 9 CP m) (Nat.xor (at' 9 CP k) (at' 9 CP l))) &&
        ixAll 21 fun k' => ixAll 21 fun l' => !Nat.blt k' l' || (Nat.beq k k' && Nat.beq l l') ||
          !Nat.beq (Nat.xor (at' 9 CP k) (at' 9 CP l)) (Nat.xor (at' 9 CP k') (at' 9 CP l'))))

@[expose] noncomputable def ixValid (CP S2 : Nat) :
    List Nat → List (Nat × Nat × Nat × Nat × Nat) → Bool :=
  fun K L => List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun st _ ih K => K.contains st.2.1 && K.contains st.2.2.1 && K.contains st.2.2.2.1 &&
      K.contains st.2.2.2.2 && Nat.blt st.1 21 &&
      ixAll 21 (fun z => (ivP CP S2 z st.2.1 st.2.2.1 && ivP CP S2 z st.2.2.2.1 st.2.2.2.2) ==
        Nat.beq z st.1) &&
      ih (st.1 :: K)) L K

end CFSG.SmithE.K
