module

public import Certificates.Data.Kernel.OpsMcertT

public section

namespace CFSG.KC.OpsMT

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsK CFSG.KC.OpsMN

variable {V : Type} (O : Ops Nat V)

@[expose] noncomputable def seedsXT (A B : Nat) (C : MCert) (rA rB : Nat) (C' : MCert)
    (xs : List (Nat × Word)) : Bool :=
  C'.prog.all (Op.lt C'.nregs) && xs.all (fun q => decide (q.1 < C.nregs) && wordLt C'.nregs q.2) &&
    regsT O A B C.nregs C.prog fun T => certG O (getR T) C && O.eq (getR T rA) A &&
      O.eq (getR T rB) B && regsT O A B C'.nregs C'.prog fun T' =>
        xs.all fun q => O.eq (getR T q.1) (evalWG O (getR T') q.2)

end CFSG.KC.OpsMT

end
