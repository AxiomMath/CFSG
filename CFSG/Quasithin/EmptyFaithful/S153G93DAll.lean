module

public import CFSG.Quasithin.EmptyFaithful.S153G93DMain
public import CFSG.Quasithin.EmptyFaithful.S153G93DCovLinD
public import CFSG.Quasithin.EmptyFaithful.S153G93DCovPerm
public import CFSG.Quasithin.EmptyFaithful.S153G93DCovL42
public import CFSG.Quasithin.EmptyFaithful.S153G93DCovG2
public import CFSG.Quasithin.EmptyFaithful.S153G93DSizes
public import CFSG.Quasithin.EmptyFaithful.S153G93DSL2N
public import CFSG.Quasithin.EmptyFaithful.S153G93DG2N
public import CFSG.Quasithin.EmptyFaithful.S153G93DExtSq5
public import CFSG.Quasithin.EmptyFaithful.S153G93DHRows
public import CFSG.Quasithin.EmptyFaithful.S153G93DHat
public import CFSG.Quasithin.EmptyFaithful.S153G93DOrthMain
public import CFSG.Quasithin.EmptyFaithful.S153G93DSL2CMain
public import CFSG.Quasithin.EmptyFaithful.S153G93DL32
public import CFSG.Quasithin.EmptyFaithful.S153G93DOm4PD
public import CFSG.Quasithin.Background.SmithD37Main

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

theorem oneCases_holds :
    OneCases where
  covSL3 := CovLin.covSL3_holds
  covSp4 := CovLin.covSp4_holds
  covAlt7 := CovPerm.covAlt7_holds
  covSym7 := CovPerm.covSym7_holds
  covL42 := CovL42.covL42_holds
  covG2One := CovG2.covG2One_holds
  covG2Der := CovG2.covG2Der_holds
  sizes := Sizes.modelSizes_holds
  sl2 := SL2N.oneSL2_holds
  g2 := G2N.oneG2_holds
  extSq5 := ExtSq5.oneExtSq5_holds
  su3 := HRows.oneSU3_holds
  sz := HRows.oneSz_holds
  orth4 := Orth.oneOrth4_of_sl2Cent SL2C.sl2Cent_holds
  m22code := HRows.oneM22Code_holds
  hat := Hat.oneHat_holds

theorem twoCases_holds : TwoCases := ⟨Om4P.twoOmega_holds, L32.twoTensor_holds⟩

theorem d37Core_holds :
    D37Core :=
  fun _ _ _ _ _ _ _ hC hnc => SmithD37.core_concl hC hnc

theorem a38TypesSimple_holds : A38TypesSimple :=
  fun _ _ h => L122A.isSimpleGroup_of_a38Types h

theorem input15358G93_holds
    (h38 : A38ForSQTKCat) (hA21 : AsA21SQTKSection) (hB45 : AsB45) : Input15358G93 :=
  input15358G93_of_inputs h38 hA21 a38TypesSimple_holds hB45 d37Core_holds oneCases_holds
    twoCases_holds

end S153G93D

end CFSG.Quasithin
