module

public import Certificates.Data.Kernel.Tower.Cls14

public section

namespace Certificates.KernelTower

@[expose] noncomputable def icB (OT RP CZ nl : Nat) : Bool :=
  allB nl fun l => !Nat.beq (oe OT (l16 RP l)) 1 || Nat.ble (lane CZ 15 32767 l) 64

@[expose] noncomputable def sqB (mul : Nat → Nat → Nat) (bc : Nat → Nat) (G IM g2 XT : Nat) : Bool :=
  Nat.beq (bc g2) g2 && Nat.beq (bit XT g2) 0 &&
    allB 4 fun i => Nat.beq (mul (bc (l16 IM i)) g2) (mul g2 (l16 G i)) &&
      Nat.beq (bit XT (l16 IM i)) (bit XT (l16 G i))

@[expose] noncomputable def cenZ (mul : Nat → Nat → Nat) (G HL m : Nat) : Bool :=
  allB 4 fun i => Nat.beq (mul (l16 HL m) (l16 G i)) (mul (l16 G i) (l16 HL m))

@[expose] noncomputable def hasT (IM g2 : Nat → Nat) (nt j c : Nat) : Bool :=
  !allB nt fun j' => !(Nat.beq (IM j') (IM j) && Nat.beq (g2 j') c)

@[expose] noncomputable def cenB (mul : Nat → Nat → Nat) (bc : Nat → Nat → Nat) (G HL : Nat)
    (IM g2 : Nat → Nat) (nt : Nat) : Bool :=
  allB 256 fun m => !cenZ mul G HL m ||
    allB nt fun j => !Nat.beq (bc j (mul (l16 HL m) (g2 j))) (mul (l16 HL m) (g2 j)) ||
      hasT IM g2 nt j (mul (l16 HL m) (g2 j))

end Certificates.KernelTower
