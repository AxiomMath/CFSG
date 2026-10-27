module

public import Certificates.Data.Asch54SporFi22
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22

open CFSG.Monster.B.Co2

@[expose] noncomputable def tGenP (i : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 (tGen i)

@[expose] noncomputable def a0GenP (k : ℕ) : Equiv.Perm (Fin 3510) := permOfArr 3510 a0Gen[k]!

@[expose] noncomputable def A0 : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure ({g | ∃ i < 9, tGenP i = g} ∪ {g | ∃ k < 2, a0GenP k = g})

@[expose] noncomputable def mP : Equiv.Perm (Fin 3510) := permOfArr 3510 mArr

end CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22
