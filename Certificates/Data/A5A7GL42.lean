module

public import Certificates.Data.A5GL42
public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

open Matrix

namespace Certificates.A5A7GL42

open Certificates.A5GL42 (Mat4 Vec4 ofCode)

@[expose] def Pset (l : List ℕ) : Set Mat4 := {m | ∃ c ∈ l, ofCode c = m}

end Certificates.A5A7GL42
