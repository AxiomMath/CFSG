module

public import Certificates.Data.S5Rows

public section

namespace Certificates.S7SocQ8

open Certificates.S5Rows

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def inRefB (refs : List (List M)) (i j : M) : Bool :=
  refs.any fun R => (q8Span i j).all fun x => decide (x ∈ R)

@[expose] def refCheck (L : List M) (refs : List (List M)) : Bool :=
  L.all fun i => L.all fun j => !q8RelB i j || inRefB refs i j

@[expose] def sigmaCheck (σ : M) (refs : List (List M)) : Bool :=
  refs.all fun R => refs.any fun R' => R.all fun r => decide (σ * r * σ⁻¹ ∈ R')

end Certificates.S7SocQ8
