module

public import Certificates.Data.Kernel.Sp62W.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62FrameData

public section

namespace CFSG.KD.Sp62F

open CFSG.KD.BfsK CFSG.KD.Sp62W CFSG.KC.Mat8P CFSG.KGroups.Sp6
  CFSG.AGLEmbedding.KFactProofs.Sp62Local

@[expose] def decC (x : Nat) : List Nat := (unpackM x).take 6

@[expose] def blkAll (f : Nat → Bool) (a len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => f (Nat.add a i) && ih) len

@[expose] def fN (BL : List (List Nat)) (c : List Nat) : Bool :=
  genB c && (!(gensB.all (commB c)) || BL.contains c) &&
    (BL.contains c || powC c 81 != oneC || gensN.any fun n => powC (commC c n) 81 != oneC)

end CFSG.KD.Sp62F

end
