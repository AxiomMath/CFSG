module

public import CFSG.Milestones.ASVolI.F48.D43.Defs

public section

namespace CFSG.ASVolI

@[expose] noncomputable def burnsideF48dE_σ (j : ℕ) : Equiv.Perm (Fin 26572) :=
  if j = 2 then burnsideF48d_frob else burnsideF48d_σ (if j < 2 then j else j - 1)

end CFSG.ASVolI
