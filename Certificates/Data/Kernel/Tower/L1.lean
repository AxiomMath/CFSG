module

public import Certificates.Data.Kernel.Tower.W

public section

namespace Certificates.KernelTower

@[expose] def bit (T i : Nat) : Nat := Nat.land (Nat.shiftRight T i) 1

@[expose] noncomputable def cntB (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec 0 (fun c acc => Nat.add (cond (f c) 1 0) acc) n

@[expose] noncomputable def cntW (SM AC x : Nat) : Nat :=
  cntB 8192 fun c => Nat.beq (wm SM AC x c) (wm SM AC c x)

@[expose] noncomputable def ninvW (SM AC x : Nat) : Nat :=
  cntB 8192 fun c => !Nat.beq c 0 && Nat.beq (wm SM AC c c) 0 &&
    Nat.beq (wm SM AC x c) (wm SM AC c x)

@[expose] noncomputable def psiOK (SM PS : Nat) : Bool :=
  Nat.beq (bit PS 0) 0 && Nat.beq (bit PS 1) 1 && allB 128 fun i => allB 128 fun j =>
    Nat.beq (bit PS (lane SM 7 127 (Nat.add (Nat.mul 128 i) j))) (Nat.xor (bit PS i) (bit PS j))

@[expose] def invC (SM AC PS MR c r w : Nat) : Bool :=
  Nat.beq (wm SM AC c w) (wm SM AC w r) &&
    cond (Nat.beq (bit PS (Nat.shiftRight c 6)) 1) (Nat.beq r 64) (Nat.beq (bit MR r) 1)

@[expose] noncomputable def invOK (SM AC PS RW MR : Nat) : Bool :=
  allB 8192 fun c => Nat.beq c 0 || !Nat.beq (wm SM AC c c) 0 ||
    invC SM AC PS MR c (Nat.land (lane RW 26 67108863 c) 8191)
      (Nat.shiftRight (lane RW 26 67108863 c) 13)

@[expose] noncomputable def repN (SM AC r n : Nat) : Bool :=
  Nat.ble 256 n && (!Nat.beq n 256 || !Nat.beq (ninvW SM AC r) 87)

@[expose] noncomputable def repsOK (SM AC MR : Nat) : Bool :=
  allB 8192 fun r => Nat.beq (bit MR r) 0 || repN SM AC r (cntW SM AC r)

@[expose] noncomputable def l1OK (SM AC PS RW MR : Nat) : Bool :=
  Nat.beq (cntW SM AC 64) 128 && psiOK SM PS && invOK SM AC PS RW MR

end Certificates.KernelTower
