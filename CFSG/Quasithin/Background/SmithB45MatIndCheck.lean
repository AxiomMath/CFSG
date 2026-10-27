module

public import Certificates.Certificate260430
public import Certificates.Certificate260431
public import Certificates.Certificate260432
public import Certificates.Certificate260433
public import Certificates.Certificate260434

public section

namespace CFSG.Quasithin.B45Mat.Ind

theorem m23_ind_checks :
    m23CosetOK = true ∧ m23FlagOK 0 = true ∧ m23FlagOK 1 = true ∧ m23FlagOK 2 = true :=
  Certificates.certificate260430

theorem m23_norton_checks :
    m23NorOK 1 = true ∧ m23NorOK 2 = true ∧ m23NorOK 3 = true ∧ m23NorOK 4 = true ∧
      m23NorOK 5 = true :=
  Certificates.certificate260431

theorem m24_ind_checks :
    m24CosetOK = true ∧ m24FlagOK 0 = true ∧ m24FlagOK 1 = true ∧ m24FlagOK 2 = true :=
  Certificates.certificate260432

theorem m24_norton_checks :
    m24NorOK 1 = true ∧ m24NorOK 2 = true ∧ m24NorOK 3 = true ∧ m24NorOK 4 = true ∧
      m24NorOK 5 = true :=
  Certificates.certificate260433

theorem amal34_checks : amalOK = true :=
  Certificates.certificate260434

end CFSG.Quasithin.B45Mat.Ind
