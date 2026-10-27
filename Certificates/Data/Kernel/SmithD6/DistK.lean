module

public import Certificates.Data.Kernel.SmithD6.RankCheck
public import Certificates.Data.Kernel.SmithD6.UwData
public import Certificates.Data.Kernel.KeyTreeChunks
public import Certificates.Data.Kernel.PkTree

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree

@[expose] noncomputable def d6DistGo (B0 : Array Nat) (Bs : List (Array Nat)) :
    List (Array Nat) → Nat → Bool :=
  List.rec (motive := fun _ => List (Array Nat) → Nat → Bool) (fun _ _ => true)
    (fun B _ ih Ps v => List.rec (motive := fun _ => Bool) false
      (fun P Ps' _ => bAnd(Nat.beq (kcDist (kcMeetA B0 B P)) (pkGet JU.uwK 2 v),
        strictKB (Nat.succ v) (ih Ps'))) Ps) Bs

@[expose] noncomputable def d6DistOK (c : Nat) : Bool :=
  d6DistGo (d6PB 0) (nthA J.pbC c) (nthA J.ppC c) (Nat.mul 2048 c)

end CFSG.KD.SmithD6

end
