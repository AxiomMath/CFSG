module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbDefs

public section

namespace CFSG.KC.OrbK

open CFSG.AGLEmbedding.R3

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def vcode (p : Nat) (v : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add x (Nat.mul p ih)) v

@[expose] noncomputable def vdec (p n : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih c => Nat.mod c p :: ih (Nat.div c p)) n

@[expose] noncomputable def dotK (a : List Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun a _ ih x => List.rec (motive := fun _ => Nat) 0
      (fun x xs _ => Nat.add (Nat.mul a x) (ih xs)) x) a

@[expose] noncomputable def mvK (p n : Nat) (v : List Nat) (k : Nat) : List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun _ ih M => Nat.mod (dotK M v) p :: ih (M.drop n)) k

@[expose] def vecOK (p n : Nat) (v : List Nat) : Bool :=
  Nat.beq v.length n && v.all fun x => Nat.blt x p

@[expose] noncomputable def orbKAux (p W n nacts FULL : Nat) (m : NMod) (orb : List (Nat × Nat)) :
    Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ _ S => Nat.beq (Nat.lor S 1) FULL)
    (fun st _ ih T len S => Nat.blt st.1 nacts && Nat.blt st.2 len &&
      strictB (vcode p (mvK p n (vdec p n (Nat.mod (Nat.shiftRight T (Nat.mul W st.2)) (2 ^ W))) n
        (m.acts.getD st.1 default).mat)) fun c =>
      strictB (Nat.add T (Nat.shiftLeft c (Nat.mul W len))) fun T' =>
      strictB (Nat.lor S (Nat.shiftLeft 1 c)) fun S' =>
      strictB (Nat.succ len) fun len' => ih T' len' S') orb

@[expose] noncomputable def orbKIni (p W n nacts FULL : Nat) (m : NMod) (orb : List (Nat × Nat))
    (vs : List (List Nat)) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool) (orbKAux p W n nacts FULL m orb)
    (fun v _ ih T len S => vecOK p n v &&
      strictB (vcode p v) fun c =>
      strictB (Nat.add T (Nat.shiftLeft c (Nat.mul W len))) fun T' =>
      strictB (Nat.lor S (Nat.shiftLeft 1 c)) fun S' =>
      strictB (Nat.succ len) fun len' => ih T' len' S') vs

@[expose] noncomputable def orbK (p W : Nat) (m : NMod) (known : List (List Nat))
    (orb : List (Nat × Nat)) : Bool :=
  Nat.ble 2 p && Nat.ble (p ^ m.basis.length) (2 ^ W) &&
    strictB m.basis.length fun n => strictB m.acts.length fun nacts =>
    strictB (2 ^ p ^ n - 1) fun FULL => orbKIni p W n nacts FULL m orb known 0 0 0

end CFSG.KC.OrbK

end
