module

public import Certificates.Data.Kernel.Misc.RuCoverNetW
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.CentCoverNative
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.SeededRelations
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Presentation.Common

public section

namespace CFSG.KC.Misc.RuCoverNet

open CFSG.EvenSporadicStandard.TwoRu.CentCover

@[expose] def memW (k : Nat) : List Int :=
  Bool.rec (motive := fun _ => List Int)
    (Bool.rec (motive := fun _ => List Int)
      (Bool.rec (motive := fun _ => List Int)
        (Bool.rec (motive := fun _ => List Int) [3, 3] zW (Nat.blt k 79))
        (commW (jW ((k - 42) / 6)) (jW ((k - 42) % 6))) (Nat.blt k 78))
      (jW (k - 36) ++ jW (k - 36)) (Nat.blt k 42))
    (jW (k / 6) ++ fW (k % 6) ++ invW (jW (k / 6))) (Nat.blt k 36)

@[expose] def cosU (k i : Nat) : List Int := invW (gW (k / 16)) ++ gW (k % 16) ++ fW i

@[expose] def cosV (k i : Nat) : List Int := fW i ++ invW (gW (k / 16)) ++ gW (k % 16)

end CFSG.KC.Misc.RuCoverNet

end
