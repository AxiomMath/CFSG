module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cSuzuki

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

theorem le_normalizer_of_stmt10_0_1 (h1001 : Stmt10_0_1) {G : Type} [Group G] [Finite G]
    {T Kp Ip : Subgroup G} (hfsu : FSU G T Kp Ip) : T ≤ Subgroup.normalizer (Kp : Set G) :=
  h1001 G T Kp hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow hfsu.maximal hfsu.faithful
    hfsu.quasisimple

theorem l2SuzukiMovedFF_of (h1001 : Stmt10_0_1) : L2SuzukiMovedFF :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfsu hT _ _ => hT (le_normalizer_of_stmt10_0_1 h1001 hfsu)

theorem l2SuzukiMovedFour_of (h1001 : Stmt10_0_1) : L2SuzukiMovedFour :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfsu hT _ => hT (le_normalizer_of_stmt10_0_1 h1001 hfsu)

theorem l2Suzuki_of_ten
    (hF : A312Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hM : FactMathieuOrders) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (hG2 : FactG2Simple)
    (h1001 : Stmt10_0_1) : L2Suzuki :=
  l2Suzuki_of hF h36 h37 h39 hM h325 h328 hG2 (l2SuzukiMovedFF_of h1001)
    (l2SuzukiMovedFour_of h1001)

end CFSG.Quasithin.Vol2.Ch11.SecB
