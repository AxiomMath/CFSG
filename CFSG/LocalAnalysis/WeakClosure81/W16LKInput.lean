module

public import CFSG.LocalAnalysis.WeakClosure81.W16LKPair
public import CFSG.Quasithin.Background.F918Z4c1Sz

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem kGroup1616Input_holds :
    KGroup1616Input where
  sz_simple := fun n X _ _ h =>
    (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n h).2
  sz_card := fun n X _ _ h => by
    rw [CFSG.Quasithin.card_of_isSz h]
    ring
  u3_sylow_ti := fun n X _ _ _ hX R R' hne => hX.sylow_inf_eq_bot hne
  u3_center_card := fun n X _ _ _ hX R => hX.card_sylowCenter R
  u3_omega := fun n X _ _ _ hX R g hg => hX.mul_self_eq_one_iff R hg
  u3_card_sylow := fun n X _ _ _ hX => hX.card_sylow
  u3_pair := fun n X _ _ _ hX R R' hne => hX.isL2Pair_sylowCenter_sup hne

end CFSG.LocalAnalysis.WeakClosure81

end
