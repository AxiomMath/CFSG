module

public import Certificates.Data.Kernel.Census.PackedF
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.J1
  "Certificates/Kernel/Census/J1/data/j1.json.gz" 6084752 1067584761690296969
  (j1GP : Array Nat) (j1Prog : List (Nat × Nat)) (j1SG : Array Nat) (j1Nodes : Array FNodeP)
  (j1CS : ArrCertP) (j1RegsP : Array Nat)

public section

namespace CertificateChecks.KernelCensus.J1

open CFSG.KC.Census

@[expose] noncomputable def inXP (P : Nat) : Bool := pinXL j1RegsP P

@[expose] noncomputable def stepF (t : Nat) : Bool :=
  Nat.beq j1RegsP[4 + t]! (pc 3080 12 j1RegsP[(j1Prog.getD t (0, 0)).1]!
    j1RegsP[(j1Prog.getD t (0, 0)).2]!)

@[expose] noncomputable def nodeF (k : Nat) : Bool := pfullOK 3080 12 inXP j1GP j1Nodes[k]!

@[expose] noncomputable def pairF (i : Nat) : Bool :=
  ppairsAt 3080 12 [0, 1, 2] j1Nodes j1CS j1CS.pts[i]!

end CertificateChecks.KernelCensus.J1

end
