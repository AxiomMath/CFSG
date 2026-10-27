module

public import CFSG.Quasithin.Background.FourListSporadicPf
public import CFSG.Milestones.FAM_M_finiteness
public import CFSG.Sporadic.Bridge.Y443Relabel

public section

namespace CFSG.Quasithin.FourListSporadic

theorem card_carrier_monster :
    Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M) =
      808017424794512875886459904961710757005754368000000000 :=
  (Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv).trans
    (CFSG.Milestones.fam_m_finiteness.trans (by norm_num [CFSG.Open.monsterOrder]))

theorem sporadicFourListDisjoint_holds :
    SporadicFourListDisjoint :=
  sporadicFourListDisjoint_of_card_monster card_carrier_monster

end CFSG.Quasithin.FourListSporadic
