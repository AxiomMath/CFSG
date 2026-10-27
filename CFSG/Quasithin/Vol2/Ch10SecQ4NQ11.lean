module

public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ10
public import CFSG.Quasithin.Vol2.Ch10SecQ4A25

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.G3

theorem obl10_2_1E4A314_holds'
    (hF1 : FactA314NoSL25Block) (hF2 : FactA314B45)
    (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h318 : A318Facts) (h36' : A36ForSQTK)
    (hA7 : Ch11.SecA.FactA7Cent) (h311 : Theorem311Stmt) (h331 : Stmt3_3_1)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hshape : Stmt7_0_1_shape) : Obl10_2_1E4A314 :=
  obl10_2_1E4A314_holds hF1 hF2 (obl10_2_1E4Nonquasi_of h311 h331 h36 h37 h38 h39 hshape h113)
    h113 h37 h38 h318 h36' hA7

end CFSG.Quasithin.Vol2.Ch10.SecF
