module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Inputs
public import CFSG.Milestones.ASVolI.F48.Small.EngCheck

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.HNOddCore

@[expose] def burnsideF48t_g23X : Subgroup (Equiv.Perm (Fin 728)) :=
  arrGen 728 (burnsideF48t_g23Gens ())

@[expose] def burnsideF48t_g23P1' : Subgroup (Equiv.Perm (Fin 728)) :=
  arrGen 728 burnsideF48t_g23P1Arr

@[expose] def burnsideF48t_g23P2' : Subgroup (Equiv.Perm (Fin 728)) :=
  arrGen 728 burnsideF48t_g23P2Arr

@[expose] def burnsideF48t_g23B' : Subgroup (Equiv.Perm (Fin 728)) :=
  arrGen 728 burnsideF48t_g23BArr

@[expose] def burnsideF48t_g23S0' : Subgroup (Equiv.Perm (Fin 728)) :=
  arrGen 728 (burnsideF48t_g23S0Arr ())

@[expose] def burnsideF48t_g23K' : Subgroup (Equiv.Perm (Fin 728)) :=
  arrGen 728 (burnsideF48t_g23KArr ())

@[expose] noncomputable def burnsideF48t_g23σ (i : ℕ) : Equiv.Perm (Fin 728) :=
  CFSG.ONSchreier.permOfArr 728 burnsideF48t_g23LArr[i]!

@[expose] noncomputable def burnsideF48t_g23γ (i : ℕ) : Equiv.Perm (Fin 728) :=
  CFSG.ONSchreier.permOfArr 728 (burnsideF48t_g23Gens ())[i]!

@[expose] noncomputable def burnsideF48t_g23τ : Equiv.Perm (Fin 728) :=
  CFSG.ONSchreier.permOfArr 728 burnsideF48t_g23Tau

@[expose] noncomputable def burnsideF48t_g23κ (i : ℕ) : Equiv.Perm (Fin 728) :=
  burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_g23σ l) (burnsideF48t_g23KW.getD i [])

end CFSG.ASVolI
