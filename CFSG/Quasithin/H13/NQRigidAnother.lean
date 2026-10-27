module

public import CFSG.Quasithin.H13.NQRigidThompson
public import CFSG.Quasithin.H13.NQCoreAnotherMaxLocal

public section

namespace CFSG.Quasithin.H13.NQRigid

open CFSG.Open CFSG.QuasithinUnique

theorem stmtAnotherMaximalTwoLocal_of_modelReduction
    (h3 : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G) :
    StmtAnotherMaximalTwoLocal :=
  fun _ _ _ _ _ _ h => NQCore.nq_original_configuration_has_another_maximal_two_local h3 h

end CFSG.Quasithin.H13.NQRigid
