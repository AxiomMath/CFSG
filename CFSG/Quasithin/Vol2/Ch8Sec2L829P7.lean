module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822A
public import CFSG.Quasithin.Vol2.Ch8Sec2L829L3M22

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L829P7

theorem stmt8_2_2P7_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) : Stmt8_2_2P7 := by
  intro G _ _ T L I hyp _ _ hc hrow H h k hH _ _
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  exact (setting_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp hTL hH).2.2.2

theorem step829Cocode_of' (hmod : StmtFSUModule) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal)
    (hsweep : Cocode829Sweep) : Step829Cocode :=
  step829Cocode_of hmod (stmt8_2_2P7_of h37 h38 h39 h3228 h325 h331 hC58 h317 h711n) hsweep

theorem step829L3M22_of' (hmod : StmtFSUModule) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal)
    (hns : L3M22Nonsolv) (hsolv : L3M22Solv) : Step829L3M22 :=
  step829L3M22_of hmod (stmt8_2_2P7_of h37 h38 h39 h3228 h325 h331 hC58 h317 h711n) hns hsolv

end L829P7

end CFSG.Quasithin.H13
