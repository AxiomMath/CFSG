module

public import CFSG.Quasithin.Background.FFC3Assembly
public import CFSG.Quasithin.Background.SmithB51LnMain
public import CFSG.Quasithin.Background.SmithB51Sp4
public import CFSG.Quasithin.Background.SmithB51P2
public import CFSG.Quasithin.Background.SmithB51P5
public import CFSG.Quasithin.Background.F918D9
public import CFSG.Quasithin.Background.SmithB49
public import CFSG.Quasithin.Background.SmithA36
public import CFSG.Quasithin.Background.SmithB51G2DMain

public section

namespace CFSG.Quasithin

namespace B5

theorem asB51_of_open
    (hB42 : AsB42) (hSL3 : AsB51NonirrSL3IH) : AsB51 :=
  have hA36 := asA36NoOddCover_holds
  have hG2 := asB51G2Dual_holds hB42
  have hI := FFC.b51IrrInputs_of_ffc hB42 asI16Cover_of FFC.asB51NonsplitOffSp4_holds
  have hLn := asB51NonirrLnIH_holds asA21SQTKSection hB42 asI16Cover_of asB492Split_holds
  FFC.asB51_of_ffc' hB42 asI16Cover_of FFC.asB51NonsplitOffSp4_holds hA36
    (asB51NonirrSL3_of_ind hI asA21SQTKSection hA36 hSL3 hLn)
    (asB51NonirrLn_of_ind hI asA21SQTKSection hA36 hSL3 hLn) asB51P2_holds
    (asB51P5_of_p2 (FFC.b51IrrInputs_of_ffc hB42 asI16Cover_of FFC.asB51NonsplitOffSp4_holds) hG2
        asB51P2_holds)

end B5

end CFSG.Quasithin
