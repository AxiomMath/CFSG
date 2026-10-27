module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenNineSpec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6PGL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6M10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Aut
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenNineDataPGL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenNineDataM10
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenNineDataAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenQ9

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.LocalAnalysis.WeakClosure81.NFA6

theorem fourTenModel_pgl29 : FourTenModel A6Models.pgl29 PGLModel.T₀ :=
  fourTenModel_of_check PGLModel.desc_T PGLModel.sylow PGLModel.sup_eq PGLTable.seed_ok
    PGLTable.ens_ok

theorem fourTenModel_m10 : FourTenModel A6Models.m10 M10Model.T₀ :=
  fourTenModel_of_check M10Model.desc_T M10Model.modelFacts.sylow M10Model.modelFacts.sup_eq
    M10Table.seed_ok M10Table.ens_ok

theorem fourTenModel_autA6 : FourTenModel A6Models.autA6 P0 :=
  fourTenModel_of_check AutModel.desc_T AutModel.sylow AutModel.sup_eq AutTable.seed_ok
    AutTable.ens_ok

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenQ9
