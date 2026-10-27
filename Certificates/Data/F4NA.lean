module

public import Certificates.Data.F4ThreeRank

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.LieType.Simplicity.TitsBits

namespace F4SylowCert

variable (c : F4SylowCert)

@[expose] def wt (w : List ℕ) (i : ℕ) : ℕ :=
  ((c.paths.getD i []).map fun g => w.getD g 0).sum % 3

@[expose] def homOK (w : List ℕ) : Bool :=
  (List.range 729).all fun i => (List.range 6).all fun g =>
    decide (c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3)

end F4SylowCert

@[expose] def f4WA : List ℕ := [0, 0, 0, 0, 1, 0]

@[expose] def f4WB : List ℕ := [1, 1, 1, 0, 0, 2]

@[expose] def f4WC : List ℕ := [0, 0, 0, 0, 1, 2]

@[expose] def f4WY2 : List ℕ := [0, 0, 0, 0, 0, 1]

@[expose] def f4NaZ : ℕ := 39

@[expose] def f4ZaList : List ℕ := [0, 39, 134, 147, 218, 365, 416, 482, 594]

@[expose] def f4ZcList : List ℕ := [0, 39, 130, 162, 208, 373, 395, 490, 594]

@[expose] def f4ShortPos : List ℕ :=
  [2, 3, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31, 35, 36, 37, 40, 41, 44, 45, 48, 49,
    51]

@[expose] def trIB (A : ℕ) : Bool :=
  f4ShortPos.foldr (fun p b => xor (A.testBit (52 * p + p)) b) false

@[expose] def cubeF (tb : ℕ → ℕ) (i : ℕ) : Bool :=
  decide (mul (mul (tb i) (tb i)) (tb i) % 2 ^ 2704 = oneBits % 2 ^ 2704)

@[expose] def commF (tb : ℕ → ℕ) (i j : ℕ) : Bool :=
  decide (mul (tb i) (tb j) % 2 ^ 2704 = mul (tb j) (tb i) % 2 ^ 2704)

@[expose] def qF (tb : ℕ → ℕ) (i : ℕ) : Bool :=
  !trIB (tb i) && !trIB (mul (tb i) (tb f4NaZ)) && !trIB (mul (mul (tb i) (tb f4NaZ)) (tb f4NaZ))

@[expose] def uniqF (tb : ℕ → ℕ) (e3 : List ℕ) (i : ℕ) : Bool :=
  let C := e3.filter fun j => commF tb j i
  decide (C.length ≤ 81) && (decide (C.length < 81) || C.any fun x => C.any fun y => !commF tb x y)

namespace F4SylowCert

variable (c : F4SylowCert)

@[expose] def naCheckWith (tb : ℕ → ℕ) : Bool :=
  let r := List.range 729
  let e3 := r.filter fun i => cubeF tb i
  c.homOK f4WA && c.homOK f4WB && c.homOK f4WC && c.homOK f4WY2 &&
  r.all (fun i => cubeF tb i == (c.wt f4WA i == 0 || c.wt f4WB i == 0 || c.wt f4WC i == 0)) &&
  decide ((r.filter fun i => c.wt f4WA i == 0).length = 243) &&
  decide ((r.filter fun i => c.wt f4WB i == 0).length = 243) &&
  decide ((r.filter fun i => c.wt f4WC i == 0).length = 243) &&
  decide ((r.filter fun i => c.wt f4WA i == 0 && c.wt f4WY2 i == 0).length = 81) &&
  (c.wt f4WB f4NaZ == 0 && decide (f4NaZ ≠ 0) && cubeF tb f4NaZ &&
    r.all (fun j => c.wt f4WB j != 0 || commF tb f4NaZ j) && trIB (tb f4NaZ)) &&
  (decide (f4ZaList.length = 9) && decide f4ZaList.Nodup &&
    f4ZaList.all (fun z => decide (z < 729) && c.wt f4WA z == 0 &&
      r.all fun j => c.wt f4WA j != 0 || commF tb z j)) &&
  (decide (f4ZcList.length = 9) && decide f4ZcList.Nodup &&
    f4ZcList.all (fun z => decide (z < 729) && c.wt f4WC z == 0 &&
      r.all fun j => c.wt f4WC j != 0 || commF tb z j)) &&
  decide ((r.filter fun i => c.wt f4WB i == 0 && qF tb i).length = 24) &&
  decide ((r.filter fun i => c.wt f4WA i == 0 && c.wt f4WY2 i == 0 && decide (i ≠ 0) &&
    !trIB (tb i)).length = 24) &&
  r.all (fun i => !cubeF tb i || (c.wt f4WA i == 0 && c.wt f4WY2 i == 0) || uniqF tb e3 i)

@[expose] def tabArr : Array ℕ := (c.tabList c.gbList).toArray

@[expose] def naCheck : Bool :=
  let T := c.tabArr
  c.naCheckWith fun i => T.getD i 0

end F4SylowCert

@[expose] def F4NACheck : Prop := f4ThreeCert.naCheck = true

end CFSG.RankThree.PartOne.F106
