module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Data.TriD4TwoRow
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Open.LocalVocabulary

public section

namespace CertificateChecks.KernelD4

meta def lcFX : List Nat :=
  open CFSG.StandardType.TriD4TwoRow CFSG.Monster.B.Co2.Native in
  [CFSG.KS.RawGen.pack 12 (f0Arr ()), CFSG.KS.RawGen.pack 12 (compA 2457 (f0Arr ()) (phiInvArr ())),
    CFSG.KS.RawGen.pack 12 (rowArr 49), CFSG.KS.RawGen.pack 12 (rowArr 50),
    CFSG.KS.RawGen.pack 12 (rowArr 51), CFSG.KS.RawGen.pack 12 (rowArr 52)]

end CertificateChecks.KernelD4

end

#kss_natlist CertificateChecks.KernelD4.FX CertificateChecks.KernelD4.lcFX

#kc_repo #kc_json_gz CFSG.KD.D4F "Certificates/Kernel/D4/data/field.json.gz" 9692 8585180994262485624
  (NJ : List Nat) (ZO : List Nat) (ZL : List (List Nat)) (ZC : List (List Nat)) (ZP : List (List (Nat × Nat))) (CD : List (List Nat))
  (CR : List (Nat × Nat)) (CN : List (List Nat)) (CW : List (List (Nat × (List Nat × Nat))))
