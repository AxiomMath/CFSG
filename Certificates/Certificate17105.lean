module

public import CFSG.Monster.Existence.StdOdd.Cert.Reps
import Certificates.Kernel.StdOdd.Comm7B.Glue

public section

namespace Certificates

open CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.Cert in
theorem certificate17105 :     ∃ z ∈ Subgroup.centralizer ({rep7B} : Set Rgrp),
      Nat.card ↥(Subgroup.centralizer ({rep7B} : Set Rgrp) ⊓
        Subgroup.centralizer ({z} : Set Rgrp)) = 49 :=
  CFSG.KD.StdOdd.Comm7B.exists_card_inf_centralizer_rep7B_K

end Certificates
