module

public import Certificates.Data.U6ThreeRank

public section

namespace CFSG.RankThree.PartOne.F106

namespace U6Mon

@[expose] def cubeB (x : U6Mon) : Bool := decide ((x.mul x).mul x = one)

@[expose] def blk (x : U6Mon) : ZMod 3 := x.d0 + x.d1 + x.d2

@[expose] def zc : U6Mon := ⟨0, 0, 0, 1, 1, 1, 0, 0⟩

@[expose] def penc (a : ZMod 3) : ZMod 2 × ZMod 2 :=
  match a.val with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | _ => (1, 1)

@[expose] def trSum (x : U6Mon) : ZMod 2 × ZMod 2 :=
  ∑ i : Fin 6, if i = u6Perm x.t i then penc (x.d i) else 0

@[expose] def trB (x : U6Mon) : Bool := decide (x.trSum = 0)

@[expose] def qB (x : U6Mon) : Bool :=
  !x.trB && !(x.mul zc).trB && !((x.mul zc).mul zc).trB

@[expose] def commB (x y : U6Mon) : Bool := decide (x.mul y = y.mul x)

end U6Mon

@[expose] def u6NaZ : ℕ := 19

namespace U6SylowCert

variable (c : U6SylowCert)

@[expose] def uniqOK (g : ℕ → U6Mon) (e3 : List ℕ) (i : ℕ) : Bool :=
  let C := e3.filter fun j => U6Mon.commB (g j) (g i)
  decide (C.length ≤ 81) &&
    (decide (C.length < 81) || C.any fun x => C.any fun y => !U6Mon.commB (g x) (g y))

@[expose] def naCheckWith (g : ℕ → U6Mon) : Bool :=
  let r := List.range 729
  let e3 := r.filter fun i => (g i).cubeB
  decide ((r.filter fun i => (g i).cubeB).length = 297) &&
  decide ((r.filter fun i => decide ((g i).blk = 0)).length = 243) &&
  r.all (fun i => !decide ((g i).blk = 0) || (g i).cubeB) &&
  decide (U6Mon.zc.blk = 0) && U6Mon.zc.cubeB && decide (U6Mon.zc ≠ U6Mon.one) &&
  decide (u6NaZ < 729 ∧ g u6NaZ = U6Mon.zc) && U6Mon.one.trB &&
  r.all (fun i => U6Mon.commB (g i) U6Mon.zc) &&
  decide ((r.filter fun i => decide ((g i).blk = 0) && (g i).qB).length = 48) &&
  decide ((r.filter fun i => decide ((g i).t0 = 0 ∧ (g i).t1 = 0)).length = 81) &&
  decide ((r.filter fun i => decide ((g i).t0 = 0 ∧ (g i).t1 = 0) && decide (i ≠ 0) &&
    (g i).trB).length = 30) &&
  r.all (fun i => decide ((g i).t0 = 0 ∧ (g i).t1 = 0) || uniqOK g e3 i)

@[expose] def tabArr : Array U6Mon := ((List.range 729).map c.tab).toArray

@[expose] def naCheck : Bool :=
  let T := c.tabArr
  naCheckWith fun i => T.getD i U6Mon.one

end U6SylowCert

@[expose] def U6NACheck : Prop := u6ThreeCert.naCheck = true

end CFSG.RankThree.PartOne.F106
