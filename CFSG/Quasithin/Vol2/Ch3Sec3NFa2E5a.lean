module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E5aK
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E5aL

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)

theorem leaf_E5a_of (h36 : A36ForSQTK) (h5 : Stmt3_3_5)
    (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q → E5aConcl L K T H := by
  intro G _ _ T M L D H K q c
  exact c.E5a_of_comm_comm h36 (c.comm_comm_R_le_Z h36 h5 h9 hGA h128 h37 h38 h39)

end CFSG.Quasithin.H13.NFa2
