module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Quasithin

open CFSG.CosetTable

@[expose] def coxWord {n : ℕ} (i j : Fin n) (m : ℕ) : List (Fin n × Bool) :=
  (List.replicate m [(i, true), (j, true)]).flatten

@[expose] def coxExp {n : ℕ} (i j : Fin n) : ℕ := if j.val = i.val + 1 then 3 else 2

@[expose] def coxRels (n : ℕ) : List (List (Fin n × Bool)) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j =>
      if i = j then some (coxWord i i 1)
      else if i.val < j.val then some (coxWord i j (coxExp i j)) else none

end CFSG.Quasithin
