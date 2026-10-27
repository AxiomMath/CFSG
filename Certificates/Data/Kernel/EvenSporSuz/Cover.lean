module

public import Certificates.Data.Kernel.EvenSporSuz.Defs

public section

namespace CFSG.KC.EvenSporSuz

@[expose] def invR24 (R : List ℕ) : List ℕ :=
  ((List.range 24).find? fun k => powR R (k + 1) == oneR).elim oneR fun k => powR R k

@[expose] def negR : List ℕ := (List.range 12).map fun i => 2 * 64 ^ i

@[expose] def pmR (v : List ℕ) : Bool := v == oneR || v == negR

end CFSG.KC.EvenSporSuz
