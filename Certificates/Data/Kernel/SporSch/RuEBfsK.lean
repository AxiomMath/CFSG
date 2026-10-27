module

public import Certificates.Data.Kernel.SporSch.RuImg

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def conjP (N NI x : Nat) : Nat :=
  pcomp (nat_lit 4060) (nat_lit 12) (nat_lit 4095)
    (pcomp (nat_lit 4060) (nat_lit 12) (nat_lit 4095) N x) NI

@[expose] noncomputable def ebfsGen (c h g : Nat) (s : List Nat × List Nat × List Nat) :
    List Nat × List Nat × List Nat :=
  Bool.rec (motive := fun _ => List Nat × List Nat × List Nat)
    (s.1 ++ [c], s.2.1 ++ [h], s.2.2 ++ [g]) s (memNL c s.1)

@[expose] noncomputable def ebfsRound (N0 N1 N0I N1I : Nat)
    (s : List Nat × List Nat × List Nat × Nat) : List Nat × List Nat × List Nat × Nat :=
  Bool.rec (motive := fun _ => List Nat × List Nat × List Nat × Nat)
    (s.1, s.2.1, s.2.2.1, Nat.succ s.2.2.2)
    ((fun t => (t.1, t.2.1, t.2.2, Nat.succ s.2.2.2))
      (ebfsGen (conjP N1 N1I (s.1.getD s.2.2.2 0)) s.2.2.2 1
        (ebfsGen (conjP N0 N0I (s.1.getD s.2.2.2 0)) s.2.2.2 0 (s.1, s.2.1, s.2.2.1))))
    (Nat.blt s.2.2.2 (lenNL s.1))

@[expose] noncomputable def ebfsRun (N0 N1 N0I N1I Z k : Nat) :
    List Nat × List Nat × List Nat × Nat :=
  Nat.rec (motive := fun _ => List Nat × List Nat × List Nat × Nat) ([Z], [0], [0], 0)
    (fun _ s => ebfsRound N0 N1 N0I N1I s) k

@[expose] noncomputable def ebfsOut (s : List Nat × List Nat × List Nat × Nat) :
    List Nat × List Nat × List Nat :=
  (s.1, s.2.1, s.2.2.1)

@[expose] noncomputable def ebfsK (N0 N1 N0I N1I Z : Nat) : List Nat × List Nat × List Nat :=
  ebfsOut (ebfsRun N0 N1 N0I N1I Z 8)

end CFSG.KS.SporSch

end
