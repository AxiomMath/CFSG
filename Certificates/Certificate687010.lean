module

public import Certificates.Kernel.A9Mod.Final

public section

local instance (priority := high) Certificates.instAddCommGroupZMod2C687010 :
    AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

public section

namespace Certificates

open CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.A9Mod in
theorem certificate687010 : ∀ σ : alternatingGroup (Fin 9) →* Module.End (ZMod 2) V8,
    σ eltG = toLin N1 ∨ σ eltG = toLin N2 → ConjToTarget σ := CFSG.KD.A9Mod.conjToTarget_all

end Certificates
