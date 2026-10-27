module

public import Certificates.Data.E6DiagRegular

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

@[expose] def wkRho : List ℕ := [5, 1, 4, 3, 2, 0]

@[expose] def wkRows (rs : List (List ℤ)) : List (List ℤ) :=
  (List.range 6).map fun i =>
    let r := rs.getD i []
    (List.range 6).map fun k => (if i = k then 1 else 0) + r.getD (wkRho.getD k 0) 0

@[expose] def wkEnt (nl : List (List ℤ)) (i k : ℕ) : ℤ := (nl.getD i []).getD k 0

@[expose] def wkRowRoot (nl : List (List ℤ)) : Bool :=
  (List.finRange TwistTag.E6.tag.rank).any fun i =>
    decide (dotL (List.ofFn fun j => TwistTag.E6.tag.cartan i j) (nl.getD i []) = 1)

@[expose] def wkZero (nl : List (List ℤ)) : Bool :=
  (List.range 6).all fun i => (List.range 6).all fun k => wkEnt nl i k == 0

@[expose] def wkDet3 (nl : List (List ℤ)) (r c : ℕ × ℕ × ℕ) : ℤ :=
  let a := wkEnt nl r.1 c.1
  let b := wkEnt nl r.1 c.2.1
  let d := wkEnt nl r.1 c.2.2
  let e := wkEnt nl r.2.1 c.1
  let f := wkEnt nl r.2.1 c.2.1
  let g := wkEnt nl r.2.1 c.2.2
  let h := wkEnt nl r.2.2 c.1
  let i := wkEnt nl r.2.2 c.2.1
  let j := wkEnt nl r.2.2 c.2.2
  a * f * j - a * g * i - b * e * j + b * g * h + d * e * i - d * f * h

@[expose] def wkTriples : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 3, 4),
    (0, 3, 5), (0, 4, 5), (1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 5), (1, 4, 5),
    (2, 3, 4), (2, 3, 5), (2, 4, 5), (3, 4, 5)]

@[expose] def wkMinor (nl : List (List ℤ)) : Bool :=
  wkTriples.any fun r => wkTriples.any fun c => [1, -1, 2, -2].contains (wkDet3 nl r c)

@[expose] def wkTuple (T : RootTables) (t : List ℕ) : Bool :=
  let nl := wkRows (t.map fun k => T.vecs.getD k [])
  wkRowRoot nl || wkZero nl || wkMinor nl

@[expose] def wkMain (T : RootTables) (elems : List (List ℕ)) : Bool :=
  elems.all (wkTuple T)

@[expose] def e6TypeCheck (_ : Unit := ()) : Bool :=
  let S : StabCert3 := ⟨[], [], e6WKeys ()⟩
  S.check e6Certificate && wkMain (RootTables.ofCert e6Certificate) (S.elems .E6)

end CFSG.StandardType.TwE6RootKill
