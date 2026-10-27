module

public import Certificates.Data.Kernel.CoPairEq
public import Certificates.Data.CFSGNative.McL.Certificate

public section

namespace CFSG.KC.CoPair

open CFSG.F3.Native CFSG.Sporadic.McL.Native CFSG.Sporadic.VecOrbit.Native

@[expose] def decVM (c : Nat) : V := ⟨c % 2 ^ 32, c / 2 ^ 32⟩

@[expose] def mclVecOK (VL SA SB : Nat) : Prop :=
  (∀ j < 275, (decVM (f64 VL j)).wf = true ∧ f16 SA j < 275 ∧ f16 SB j < 275 ∧
    (comb 21 (transpose 21 (matA ())) (decVM (f64 VL j))).beq (decVM (f64 VL (f16 SA j))) = true ∧
    (comb 21 (transpose 21 (matB ())) (decVM (f64 VL j))).beq (decVM (f64 VL (f16 SB j))) = true) ∧
  basisOK 21 (chainQ.map fun r => decVM (f64 VL r)) basisTinv = true

end CFSG.KC.CoPair

end
