module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LKS
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE6
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE5c
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE7

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)

theorem a2Leaves_holds
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9)
    (hGA : GriessAllModelsStatement) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : A2Leaves where
  c1 := leaf_C1_of h36 h5 h7 h9 h128 h37 h38 h39
  e5c := leaf_E5c_of h36 h5 h7 h9 hGA h128 h37 h38 h39
  e6ii := leaf_E6ii_of h36 h128 h37 h38 h39
  e7 := leaf_E7_of h36 h5 h7 h9 hGA h128 h37 h38 h39
  ks1 := leaf_KS1_of h36 h5 h7 h9 hGA h128 h37 h38 h39
  ks2 := leaf_KS2_of h36 h5 h7 h9 hGA h128 h37 h38 h39

theorem obl3_3_13D12NF_a2_holds
    (h36 : A36ForSQTK) (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9)
    (hGA : GriessAllModelsStatement) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Obl3_3_13D12NF_a2 :=
  obl3_3_13D12NF_a2_of_leaves h36 h5 h7 h9 hGA h128 h37 h38 h39
    (a2Leaves_holds h36 h5 h7 h9 hGA h128 h37 h38 h39)

end CFSG.Quasithin.H13.NFa2
