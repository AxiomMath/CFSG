module

public import CFSG.Certificates.PerfectCoverBound
public import Certificates.Data.CFSGNative.Bridge.SurjA
public import CFSG.Sporadic.McL.Simple
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.Sporadic.Presentation.McL

open CFSG.CosetTable CFSG.Certificates CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped commutatorElement
open CFSG.Sporadic.McL (a b J orb rep_alpha rep_alpha_inv rep_beta actionChecks_parts)

@[expose] def hsAB : ℕ → List (ℕ × Bool)
  | 0 => [(1, true), (0, true), (1, false)]
  | 1 => [(0, true)]
  | 2 => [(1, false), (1, false), (0, true), (1, true), (1, true)]
  | _ => []

@[expose] def invL (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  w.reverse.map fun l => (l.1, !l.2)

@[expose] def expand (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  w.flatMap fun l => if l.2 then hsAB l.1 else invL (hsAB l.1)

@[expose] def commL (u v : List (ℕ × Bool)) : List (ℕ × Bool) := u ++ v ++ invL u ++ invL v

@[expose] def pos (w : List ℕ) : List (ℕ × Bool) := w.map fun i => (i, true)

@[expose] def certU : List (List ℕ) := [[1, 2, 0, 2], [0, 1, 2, 0, 2], [0, 2, 0, 2, 0]]

@[expose] def certV : List (List ℕ) :=
  [[1, 0, 2, 0, 2, 0, 1, 0, 1], [0, 1, 0, 2, 0, 2, 1, 0, 2, 0, 2],
   [1, 2, 0, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1]]

@[expose] def certWords : List (List (ℕ × Bool)) :=
  (List.range 3).map fun k => (k, false) :: commL (pos (certU.getD k [])) (pos (certV.getD k []))

end CFSG.Sporadic.Presentation.McL
