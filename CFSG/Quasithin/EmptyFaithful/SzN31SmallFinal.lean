module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmOdd
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD2
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD4
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6
public import CFSG.Quasithin.EmptyFaithful.SzN31CntMain
public import CFSG.Quasithin.EmptyFaithful.SzN31FactR
public import CFSG.Quasithin.EmptyFaithful.SzN31KC

public section

namespace CFSG.Quasithin.SzN31

theorem g94Small_of_T (hT : SylowGL6NoCover) : G94Small :=
  g94Small_of_cases hT smallCase2 smallCase4 smallCase6 smallOdd

theorem g94StmtSolv_of_T (hT : SylowGL6NoCover) : SzN29.G94StmtSolv :=
  g94StmtSolv_of_kc_counting_small (g94KC_of_factR factR) g94Counting (g94Small_of_T hT)

end CFSG.Quasithin.SzN31
