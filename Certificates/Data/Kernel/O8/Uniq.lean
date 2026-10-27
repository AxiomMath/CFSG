module

public import Certificates.Data.Kernel.O8.SA
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqWDefs

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.SplitC (UniqWit)

@[expose] noncomputable def commSA (SC i k : Nat) : Bool :=
  matMulK (saAtK SC i) (saAtK SC k) == matMulK (saAtK SC k) (saAtK SC i)

@[expose] noncomputable def conjSA (SC c a w : Nat) : Bool :=
  matMulK (saAtK SC c) (saAtK SC a) == matMulK (saAtK SC w) (saAtK SC c)

@[expose] noncomputable def invSA (SC i : Nat) : Bool :=
  i != 0 && matMulK (saAtK SC i) (saAtK SC i) == idK

@[expose] noncomputable def uniqWitK (J YI WT : Nat) (kind : List Nat)
    (conj : List (List (Nat × Nat))) (dl : List (List Nat)) (c0 : List Nat) : UniqWit where
  J := J
  y := ix13 YI
  cl i := Nat.land (Nat.shiftRight WT (Nat.add (Nat.mul 32 i) 26)) 63
  kind j := kind.getD j 2
  conj j := conj.getD j []
  dl j := dl.getD j []
  c0 := c0

end CFSG.KC.O8

end
