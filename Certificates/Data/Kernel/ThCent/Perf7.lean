module

public import Certificates.Data.Kernel.ThCent.List
public import Certificates.Data.ThSevenPerfect

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenPerfect

@[expose] noncomputable def perf7At (c rm ONE : Nat) (V : Nat → Nat) (Z i : Nat) : Bool :=
  strictF (wordR c rm ONE V sWords[i]!) fun P =>
    Nat.beq (mulB c rm P Z) (mulB c rm Z P) &&
      Nat.beq P (wordR c rm ONE V (sWords[(sIdx[i]!).1]! ++ sWords[(sIdx[i]!).2]! ++
        invW sWords[(sIdx[i]!).1]! ++ invW sWords[(sIdx[i]!).2]!))

end CFSG.KC.ThCent
