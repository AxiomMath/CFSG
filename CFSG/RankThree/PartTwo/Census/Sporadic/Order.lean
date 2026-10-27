module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Common
public import CFSG.Sporadic.Bridge.M11
public import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.J1
public import CFSG.RankThree.Asc83Table.M23
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.M23
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.HS

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint TauCeti

theorem excluded433_M11 : Excluded433 (.sporadic .M11) :=
  excluded433_sporadic_of_card (T := NativeSporadic.M11)
    (fun _ => CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv.map MulEquiv.symm)
    CFSG.Sporadic.Mathieu.card_M11 (by norm_num)

theorem excluded433_M22 : Excluded433 (.sporadic .M22) :=
  excluded433_sporadic_of_card (T := NativeSporadic.M22)
    (fun _ => CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv.map MulEquiv.symm)
    CFSG.Sporadic.Mathieu.card_M22 (by norm_num)

theorem excluded433_M23 : Excluded433 (.sporadic .M23) :=
  excluded433_sporadic_of_card (T := NativeSporadic.Carrier .M23)
    (fun _ => CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_M23)
    CFSG.RankThree.Asc83Table.M23.card_M23 (by norm_num)

theorem excluded433_J1 : Excluded433 (.sporadic .J1) :=
  excluded433_sporadic_of_card (T := NativeSporadic.J1)
    (fun _ => CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv.map MulEquiv.symm)
    CFSG.Sporadic.J1.card_J1 (by norm_num)

theorem excluded433_HS : Excluded433 (.sporadic .HS) :=
  excluded433_sporadic_of_card (T := NativeSporadic.Carrier .HS)
    (fun _ => CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_HS)
    CFSG.Sporadic.HS.card_HS (by norm_num)

end CFSG.RankThree.PartTwo.Census
