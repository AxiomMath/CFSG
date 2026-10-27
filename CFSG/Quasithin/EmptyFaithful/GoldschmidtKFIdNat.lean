module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdFam
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOddL2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOL3Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOU3Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFResidue

public section

namespace CFSG.Quasithin.SBd19F

theorem input15338Ident_native :
    Input15338Ident :=
  input15338IdentC_of_table
    (identTable_of_families CFSG.QuasithinUnique.Id2519.identFamilies_proved identOddL2_holds
      identOddL3_holds identOddU3_holds CFSG.Sporadic.J1.card_J1)

end CFSG.Quasithin.SBd19F
