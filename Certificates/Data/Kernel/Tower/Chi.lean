module

public import Certificates.Data.Kernel.Tower.T2

public section

namespace Certificates.KernelTower

@[expose] noncomputable def anyB (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec false (fun k acc => p k || acc) n

@[expose] def chiV (C c : Nat) : Nat :=
  Nat.xor (bitN par64 (Nat.land (Nat.land c 63) (Nat.land (Nat.shiftRight C 128) 63)))
    (bitN C (Nat.shiftRight c 6))

@[expose] noncomputable def parOK : Bool :=
  Nat.beq (bitN par64 0) 0 && allB 64 fun a => allB 64 fun b =>
    Nat.beq (bitN par64 (Nat.xor a b)) (Nat.xor (bitN par64 a) (bitN par64 b))

@[expose] noncomputable def chiWOK (SM AC C : Nat) : Bool :=
  (allB 128 fun i => allB 128 fun j =>
    Nat.beq (bitN C (lane SM 7 127 (Nat.add (Nat.mul 128 i) j))) (Nat.xor (bitN C i) (bitN C j))) &&
      allB 128 fun i => allB 64 fun v =>
        Nat.beq (bitN par64 (Nat.land (lane AC 6 63 (Nat.add (Nat.mul 64 i) v))
            (Nat.land (Nat.shiftRight C 128) 63)))
          (bitN par64 (Nat.land v (Nat.land (Nat.shiftRight C 128) 63)))

@[expose] noncomputable def chiXOK (CL : Nat → Nat) (FA g GS T : Nat) : Bool :=
  anyB 16 (fun i => Nat.beq T (CL i) ||
      Nat.beq T (Nat.add (CL i) 21778071482940061661655974875633165533184)) &&
    allB 4 (fun i => Nat.beq (chiV T (l16 FA (l16 GS i))) (chiV T (l16 GS i))) &&
      Nat.beq (chiV T g) 0

end Certificates.KernelTower
