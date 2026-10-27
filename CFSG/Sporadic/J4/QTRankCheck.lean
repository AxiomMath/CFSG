module

public import CFSG.Sporadic.J4.QTRankNative
public meta import CFSG.Sporadic.J4.QTRankNative
public import Certificates.Certificate4024

public section

namespace CFSG.Sporadic.J4.QT

theorem tabL_nodup : tabL.Nodup :=
  Certificates.certificate4024.1

theorem tabL_ok : ∀ t ∈ tabL, lenOK t = true :=
  Certificates.certificate4024.2.1

theorem idT_mem : idT ∈ tabL :=
  Certificates.certificate4024.2.2.1

theorem tabL_closed : ∀ t ∈ tabL, ∀ i < 4,
    compT t (kTab i) ∈ tabL ∧ compT t (kInvTab i) ∈ tabL :=
  Certificates.certificate4024.2.2.2.1

theorem kTab_ok :
    ∀ i < 4, lenOK (kTab i) = true ∧ lenOK (kInvTab i) = true :=
  Certificates.certificate4024.2.2.2.2.1

theorem fixCount_le :
    ∀ t ∈ tabL, compT t t = idT → t ≠ idT → fixCount t ≤ 128 :=
  Certificates.certificate4024.2.2.2.2.2.1

theorem tabL_length : tabL.length = 1024 :=
  Certificates.certificate4024.2.2.2.2.2.2.1

theorem kWords_letters :
    ∀ i < 4, ∀ ℓ ∈ kWords.getD i [], ℓ ∈ letters :=
  Certificates.certificate4024.2.2.2.2.2.2.2.1

theorem letterTab_ok : ∀ ℓ ∈ letters, lenOK (letterTab ℓ) = true :=
  Certificates.certificate4024.2.2.2.2.2.2.2.2.1

theorem pcSeq_lt : ∀ e < 1024, ∀ i ∈ pcSeq e, i < 4 :=
  Certificates.certificate4024.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4.QT
