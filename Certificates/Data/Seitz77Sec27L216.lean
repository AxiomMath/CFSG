module

public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216Inputs
public import CFSG.GH74.KGroups.PermCheck
public meta import CFSG.GH74.Uniqueness.SU.KI1r4F61L216Inputs
public meta import CFSG.GH74.KGroups.PermCheck

public section

namespace Certificates.Seitz77Sec27

open CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.GH74.KGroups

@[expose] def l216CommCount (E : List (Equiv.Perm (Fin 17))) (t : Equiv.Perm (Fin 17)) : ℕ :=
  (E.filter fun g => decide (g * t = t * g)).length

@[expose] def l216CensusCheck : Bool :=
  let EP := elemsT QP
  (elemsT QA).all fun t => !(decide (t * t = 1) && decide (t ≠ 1)) ||
    (if t ∈ EP then l216CommCount EP t == 16 else l216CommCount EP t == 60)

end Certificates.Seitz77Sec27
