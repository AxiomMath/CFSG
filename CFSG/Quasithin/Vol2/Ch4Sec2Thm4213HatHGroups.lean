module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatHInputs
public import CFSG.Sporadic.HeldB.InnerRestrict

public section

namespace CFSG.Quasithin.H13.Ch4.HatH

open CFSG.Sporadic.HeldB

@[expose] noncomputable def heP0Gens : List (Equiv.Perm (Fin 8330)) :=
  p0Words.map fun w => (w.map heInnerCP0).prod

@[expose] noncomputable def heP0 : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure {g | g ∈ heP0Gens}

@[expose] noncomputable def heD0 : Equiv.Perm (Fin 8330) := (d0Word.map heInnerCP0).prod

@[expose] noncomputable def heP1Gens : List (Equiv.Perm (Fin 8330)) :=
  p1Words.map fun w => (w.map heInnerCP1).prod

@[expose] noncomputable def heP1 : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure {g | g ∈ heP1Gens}

@[expose] noncomputable def heD1 : Equiv.Perm (Fin 8330) := (d1Word.map heInnerCP1).prod

end CFSG.Quasithin.H13.Ch4.HatH

end
