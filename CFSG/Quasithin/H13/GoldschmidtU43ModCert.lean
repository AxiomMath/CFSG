module

public import Certificates.Certificate4158
public import CFSG.Quasithin.H13.GoldschmidtU43EAsm2
public import CFSG.Quasithin.H13.GoldschmidtU43EVRFin
public import CFSG.Quasithin.H13.GoldschmidtU43ModStage
public import CFSG.Quasithin.H13.GoldschmidtU43ModModel

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin.H13.A6 (StmtU43Type)

theorem x0OneClass : X0OneClass :=
  x0OneClass_of_checks Certificates.certificate4158.1
    Certificates.certificate4158.2.2.1

theorem stage2HModel_card : Stage2HModel ∧ Stage2HCard :=
  stage2HModel_of_checks Certificates.certificate4158.1
    Certificates.certificate4158.2.1

theorem stmtU43Type :
    StmtU43Type :=
  stmtU43Type_of_closing (u43Model_of_checks Certificates.certificate4158.2.2.2)
      (x0OneClass_of_checks Certificates.certificate4158.1
          Certificates.certificate4158.2.2.1) u43Closing

end CFSG.Quasithin.H13.U43
