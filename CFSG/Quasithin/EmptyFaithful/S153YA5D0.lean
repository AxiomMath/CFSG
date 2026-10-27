module

public import CFSG.Quasithin.EmptyFaithful.S153YA5AU
public import CFSG.Quasithin.EmptyFaithful.S153YA5Split

public section

namespace CFSG.Quasithin.YG.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {H S L : Subgroup G} (C : Cfg H S L)
include C

theorem Q_eq : pCoreOf 2 H = blockU L ⊔ blockD S L :=
  pCoreOf_eq_blockU_sup_blockD C.hcs C.hj C.h5

theorem U_inf_D : blockU L ⊓ blockD S L = ⊥ := blockU_inf_blockD C.hcs C.hj C.h5

end Cfg

end CFSG.Quasithin.YG.AppC
