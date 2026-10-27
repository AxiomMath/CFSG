module

public import Certificates.Kernel.Census.J3.Data
public import Certificates.Kernel.Census.J3.Text

public section

namespace CertificateChecks.KernelCensus.J3

open CFSG.KC.Census CertificateChecks.KernelCensus

@[expose] noncomputable def lettersP : Array Nat :=
  #[J3S.F 0, J3S.F 1, J3S.F 2, J3S.F 3, J3S.F 4] ++ j3Si

@[expose] noncomputable def wordF (k : Nat) : Bool :=
  (j3XW.getD k []).all (fun i => Nat.blt i lettersP.size) &&
    Nat.beq j3XE[k]! (pprod 6156 13 ((j3XW.getD k []).map fun i => lettersP[i]!))

end CertificateChecks.KernelCensus.J3

end
