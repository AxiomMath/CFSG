module

public import Certificates.Certificate833201

public section

namespace CFSG.Sporadic.Co2Heavy

open CFSG.Blueprint CFSG.QuasithinUnique.Lin2.RankCert

theorem elemAbelianLt_co2 :
    ElemAbelianLt NativeSporadic.Co2 (2 ^ 11) :=
  Certificates.certificate833201

theorem elemAbelianLt_co2P :
    ElemAbelianLt ↥CFSG.Sporadic.Co2Cert.co2P (2 ^ 11) :=
  ElemAbelianLt.of_mulEquiv (X := ↥CFSG.Sporadic.Co2Cert.co2P) (Y := NativeSporadic.Co2)
    CFSG.Sporadic.Co2Cert.co2PermEquiv.symm elemAbelianLt_co2

end CFSG.Sporadic.Co2Heavy
