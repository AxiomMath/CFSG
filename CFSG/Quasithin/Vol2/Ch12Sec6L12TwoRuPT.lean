module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.Quasithin.H13.K1262Two.RuP

open CFSG.QuasithinUnique.K1.SporadicPerm

variable {Γ : Type} [Group Γ]

@[expose] def ruT1 (a b : Γ) : Γ := (slpElts a b ruProg).getD 163 1

@[expose] def ruT2 (a b : Γ) : Γ := (slpElts a b ruProg).getD 172 1

@[expose] def ruT3 (a b : Γ) : Γ := (slpElts a b ruProg).getD 185 1

end CFSG.Quasithin.H13.K1262Two.RuP
