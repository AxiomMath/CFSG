module

public import CFSG.Quasithin.H13.QTH13Slot11Parts
public import CFSG.Quasithin.Recognition.St84.IdS3A5
public import CFSG.Quasithin.Background.Harris.R1.NormGensL28Main
import CFSG.Quasithin.Recognition.St84.Gen.D42
import CFSG.Quasithin.Recognition.St84.Gen.TreeSLZData
public import CFSG.Quasithin.MS93.Burnside.Sp4HDesc
public import CFSG.Quasithin.MS93.MResOrd
public import CFSG.Quasithin.Recognition.St84.IdA5A5
public import CFSG.Quasithin.Recognition.St84.Gen.IdL2L2GenHolds
public import CFSG.Quasithin.Recognition.Stroth.SzUOfRqCaseA
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeWire
import CFSG.Quasithin.Recognition.Stroth.Str86AbEvenE1
import CFSG.Quasithin.Recognition.Stroth.Str86LemmaW
import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAMain

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.Stroth

theorem ys11_of_rqEq
    (hR : Str83RqEq) : CFSG.Yardstones.M64f425cd8476.AppendixCFInputs :=
  ys11_of_id
      (CFSG.Quasithin.MS93.MRes.asC132_of_descSp4 CFSG.Quasithin.MS93.S4L.burnsideSp4H_s34RDescSp4)
      F112R.St84.idA5A5_holds F112R.St84.idS3A5_holds F112R.St84.idL2L2Gen_holds
      (idSzL2_of_rqEq_caseAFalse hR str83G4CaseAFalse_of_caseA) (idU3L2_of_gaps
          (str86ZNotLe_of_e1_lemmaW str86E1_holds str86LemmaW_holds))
      (F112R.f112SliceS3L2_of_parts F112R.St84.idS3A5_holds F112R.y9U42 F112R.y9J2 F112R.y9AutJ2
          (F112R.St84.idS3L8_of_f112R1bLoc
              (Background.Harris.R1.f112R1bLoc_of_gens Background.Harris.R1.normGensL28Stmt_holds))
          F112R.y9D42 F112R.St84.noS3L2Big_holds)

end CFSG.Quasithin.H13

end
