module

public import Certificates.Data.A5A7GL42

public section

namespace Certificates.GL4

open Certificates.A5GL42 (Mat4)
open Certificates.A5A7GL42 (Pset)

abbrev GL4 : Type := GL (Fin 4) (ZMod 2)

@[expose] def sg (l : List ℕ) : Subgroup GL4 := Subgroup.closure {g : GL4 | (g : Mat4) ∈ Pset l}

end Certificates.GL4

end
