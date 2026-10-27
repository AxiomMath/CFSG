module

public import CFSG.Monster.Existence.StdOdd.Defs
public import CFSG.Open.GLADefs
import Certificates.Kernel.StdOdd.Cent7.C0

public section

namespace Certificates

open CFSG.Open CFSG.Monster.Existence.StdOdd in
theorem certificate17104 :     (∀ s : Rgrp, orderOf s = 7 →
      GLAPPrimeCoreOf 7 (Subgroup.centralizer ({s} : Set Rgrp)) = ⊥) ∧
    ∀ s : Rgrp, orderOf s = 7 → ∀ r ∈ Subgroup.centralizer ({s} : Set Rgrp), orderOf r ≠ 6 :=
  CFSG.KD.StdOdd.Cent7.c0Facts_K

end Certificates
