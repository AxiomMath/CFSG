module

public import Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.Packed
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.Suz
  "Certificates/Kernel/Census/Suz/data/suz.json.gz" 13734730 11955670585171265272
  (suzXs : List Nat) (suzRs : List Nat) (suzCjs : List (List Nat)) (suzBs : List (Nat × Nat))
  (suzIm : List Nat) (suzWt0 : List Nat) (suzWt1 : List Nat) (suzWt2 : List Nat)
  (suzWt3 : List Nat) (suzRoots : List (Nat × Nat))
  (suzBases : Array (Array Nat)) (suzEnts : Array (List (Nat × Nat × Nat)))
  (suzEL : List (Nat × Nat × Nat)) (suzCm : List Nat) (suzUs : Array Nat) (suzCs : Array Nat)
  (suzCi : Array Nat)

public section

namespace CertificateChecks.KernelCensus.Suz

open CFSG.KC.Census

@[expose] noncomputable def suzWt : List Nat := suzWt0 ++ suzWt1 ++ suzWt2 ++ suzWt3

@[expose] noncomputable def cNL : Array ArrCertP :=
  Array.mk (suzBases.toList.map fun b => pmaskCert 1782 11 b)

@[expose] noncomputable def entB (i a L : Nat) : Bool :=
  (((suzUs.toList.drop a).take L).zip ((suzEnts[i]!.drop a).take L)).all fun ue =>
    pentOK 1782 11 suzBases cNL suzCs suzCi i ue.1 ue.2

@[expose] noncomputable def suzEB : List (Nat × Nat × Nat) :=
  suzEL.flatMap fun t => (List.range t.2.2).map fun c => (t.1, c * t.2.1, t.2.1)

@[expose] noncomputable def ebF (j : Nat) : Bool :=
  let b := suzEB.getD j (0, 0, 0)
  entB b.1 b.2.1 b.2.2

@[expose] noncomputable def usF (c : Nat) : Bool :=
  (((suzUs.toList.drop (c * 160)).take 160).zip ((suzIm.drop (c * 160)).take 160)).all
    fun ua => Nat.beq (ppcA 1782 11 suzXs ua.2) ua.1

@[expose] noncomputable def csF (c : Nat) : Bool :=
  (((suzCs.toList.drop (c * 128)).take 128).zip ((suzCm.drop (c * 128)).take 128)).all
    fun sm => Nat.beq (ppcA 1782 11 suzXs sm.2) sm.1

@[expose] noncomputable def rootsF (c : Nat) : Bool :=
  (((suzUs.toList.drop (c * 256)).take 256).zip ((suzRoots.drop (c * 256)).take 256)).all
    fun ur => prootOKC 1782 11 suzBases cNL suzCs suzCi ur.1 ur.2

end CertificateChecks.KernelCensus.Suz

end
