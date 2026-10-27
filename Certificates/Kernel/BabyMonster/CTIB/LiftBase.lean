module

public import Certificates.Data.CFSGNative.CTIB.Lift
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.Native.Census
public import CFSG.Certificates.Kernel.BabyMonster.CTIBSmall.Extra

public section

namespace CertificateChecks.KernelBM.CTIB

open CFSG.Monster.B.CTIB.Native

@[expose] def stepA (A : Array Nat) (l : Nat) : Array Nat := autComp gArr A (genImgs l)

@[expose] noncomputable def dec23 (X : Nat) : List Nat :=
  (List.range 22).map fun i => CFSG.KC.BM.fld32 X i

@[expose] noncomputable def decA (X : Nat) : Array Nat := (dec23 X).toArray

theorem arr_of {A : Array Nat} {X : Nat} (h : (A.toList == dec23 X) = true) : A = decA X := by
  rw [← @Array.toArray_toList _ A, eq_of_beq h]
  rfl

theorem chain_step {x y : Array Nat} {L : List Nat} {a n : Nat}
    (h : ((L.drop a).take n).foldl stepA x = y) :
    (L.drop a).foldl stepA x = (L.drop (a + n)).foldl stepA y := by
  have e := List.take_append_drop n (L.drop a)
  calc (L.drop a).foldl stepA x = ((L.drop a).take n ++ (L.drop a).drop n).foldl stepA x := by
        rw [e]
    _ = (L.drop (a + n)).foldl stepA y := by rw [List.foldl_append, h, List.drop_drop]

end CertificateChecks.KernelBM.CTIB

end
