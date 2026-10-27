module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSpec
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocMain

public section

namespace CFSG.Quasithin.H13.F431.Un

theorem un5StdDatum : Un5StdDatum :=
  un5StdDatum_of (fun _ _ _ _ hF => stdTwo_un5Y hF) (fun _ _ _ _ hF => unStdV_un5Y hF)
    (fun _ _ _ _ hF ζ _ => un5StdLoc_datum hF ζ)

end CFSG.Quasithin.H13.F431.Un
