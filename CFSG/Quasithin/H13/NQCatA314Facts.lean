module

public import CFSG.Quasithin.H13.NQCatA314J2
public import CFSG.Quasithin.H13.NQCatA314HS
public import CFSG.Quasithin.H13.NQCatA314Ru
public import CFSG.Quasithin.H13.NQCatA314J1
public import CFSG.Quasithin.H13.NQCatA314A7
public import CFSG.Quasithin.H13.NQCatA314L3
public import CFSG.Quasithin.H13.NQCatA314M23
public import CFSG.Quasithin.H13.NQCatA314Lie
public import CFSG.Quasithin.H13.KGFactA314J4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Model

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique

theorem a314Facts_holds :
    A314Facts :=
  ⟨CFSG.QuasithinUnique.A5.G3.a314ModelFacts,
    ⟨desc_lie, desc_alt7, desc_sl3five, desc_l3five, desc_mathieu, desc_j1, desc_j2,
      CFSG.Quasithin.H13.KGA314J4.a314j4_holds, desc_hs, desc_ru⟩⟩

end CFSG.Quasithin.H13.NQCat.A314D
