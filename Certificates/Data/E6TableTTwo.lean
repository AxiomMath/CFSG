module

public import Certificates.Data.E6TableT

@[expose] public section

namespace Certificates.Data.E6TableTTwo

open Certificates.Data.E6TableT

def threeVarpiOne : Vec := [4, 3, 5, 6, 4, 2]

def cosetW (b : List Vec) : Bool :=
  let y := act b threeVarpiOne
  (List.range 6).all fun k => (y.getD k 0 - threeVarpiOne.getD k 0) % 3 == 0

def orbitLen (pi : List Nat) (j : Nat) : Nat := (followOrbit pi 6 j []).length

def inOrbit (pi : List Nat) (j j' : Nat) : Bool := (followOrbit pi 6 j []).contains j'

def rankOf (n : Nat) : Nat :=
  if n == 2 then 1 else if n == 6 then 2 else if n == 20 || n == 24 then 4 else if n == 30 || n == 40 then 5 else 0

end Certificates.Data.E6TableTTwo

end
