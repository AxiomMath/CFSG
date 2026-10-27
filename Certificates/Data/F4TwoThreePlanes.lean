module

public import Certificates.Data.F4TwoSeitz

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.F4TwoPlanes

open CFSG.LieType.Simplicity.TitsBits
open CFSG.RankThree.PartOne.SEITZX (codeBits matPowB targetWord)

@[expose] def eqP (A B : ℕ) : Bool :=
  decide (A % 2 ^ 2704 = B % 2 ^ 2704)

@[expose] def powPair (X Y i j : ℕ) : ℕ :=
  mul (matPowB X i) (matPowB Y j)

@[expose] def nineOK (X Y : ℕ) : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j =>
    (List.range 3).all fun k => (List.range 3).all fun l =>
      (decide (i = k) && decide (j = l)) || !eqP (powPair X Y i j) (powPair X Y k l)

structure NormGen where
  word : List ℕ
  second : Bool
  i₁ : ℕ
  j₁ : ℕ
  i₂ : ℕ
  j₂ : ℕ

@[expose] def NormGen.one : NormGen :=
  ⟨[], false, 1, 0, 0, 1⟩

structure TwoPlaneCert where
  wu : List ℕ
  wv : List ℕ
  ww : List ℕ
  wz : List ℕ
  gens : List NormGen
  targets : List (List ℕ)

@[expose] def TwoPlaneCert.planeX (c : TwoPlaneCert) (b : Bool) : List ℕ :=
  if b then c.ww else c.wu

@[expose] def TwoPlaneCert.planeY (c : TwoPlaneCert) (b : Bool) : List ℕ :=
  if b then c.wz else c.wv

@[expose] def TwoPlaneCert.prodBits (c : TwoPlaneCert) (idxs : List ℕ) : ℕ :=
  (idxs.map fun k => codeBits (c.gens.getD k NormGen.one).word).foldr (fun S acc => mul S acc)
    oneBits

@[expose] def TwoPlaneCert.relOK (c : TwoPlaneCert) (g : NormGen) : Bool :=
  eqP (mul (codeBits g.word) (codeBits (c.planeX g.second)))
      (mul (powPair (codeBits (c.planeX g.second)) (codeBits (c.planeY g.second)) g.i₁ g.j₁)
        (codeBits g.word)) &&
    eqP (mul (codeBits g.word) (codeBits (c.planeY g.second)))
      (mul (powPair (codeBits (c.planeX g.second)) (codeBits (c.planeY g.second)) g.i₂ g.j₂)
        (codeBits g.word))

@[expose] def TwoPlaneCert.check (c : TwoPlaneCert) : Bool :=
  eqP (matPowB (codeBits c.wu) 3) oneBits && eqP (matPowB (codeBits c.wv) 3) oneBits &&
  eqP (matPowB (codeBits c.ww) 3) oneBits && eqP (matPowB (codeBits c.wz) 3) oneBits &&
  eqP (mul (codeBits c.wu) (codeBits c.wv)) (mul (codeBits c.wv) (codeBits c.wu)) &&
  eqP (mul (codeBits c.wu) (codeBits c.ww)) (mul (codeBits c.ww) (codeBits c.wu)) &&
  eqP (mul (codeBits c.wu) (codeBits c.wz)) (mul (codeBits c.wz) (codeBits c.wu)) &&
  eqP (mul (codeBits c.wv) (codeBits c.ww)) (mul (codeBits c.ww) (codeBits c.wv)) &&
  eqP (mul (codeBits c.wv) (codeBits c.wz)) (mul (codeBits c.wz) (codeBits c.wv)) &&
  eqP (mul (codeBits c.ww) (codeBits c.wz)) (mul (codeBits c.wz) (codeBits c.ww)) &&
  nineOK (codeBits c.wu) (codeBits c.wv) && nineOK (codeBits c.ww) (codeBits c.wz) &&
  (List.range 3).all (fun i => (List.range 3).all fun j =>
    !eqP (codeBits c.ww) (powPair (codeBits c.wu) (codeBits c.wv) i j)) &&
  c.gens.all c.relOK &&
  (List.range 8).all fun t => eqP (c.prodBits (c.targets.getD t [])) (codeBits (targetWord t))

@[expose] def f4ThreePlanes : TwoPlaneCert where
  wu := [6, 2, 5, 0, 2, 4, 6, 5, 7, 6, 2, 6, 7, 5, 6, 4, 2, 0, 5, 2, 6, 1, 2, 7, 6, 1, 2, 4, 5, 7,
    2, 6, 2, 6, 2, 7, 5, 4, 2, 1, 6, 7, 2, 1]
  wv := [0, 3, 4, 5, 4, 6, 2, 5, 2, 4, 7, 6, 1, 2, 1, 6, 7, 4, 2, 5, 2, 6, 4, 5, 4, 3, 7, 6, 5, 0,
    2, 4, 6, 3, 5, 2, 7, 6, 2, 6, 7, 2, 5, 3, 6, 4, 2, 0, 5, 6, 7, 0]
  ww := [1, 6, 2, 5, 0, 7, 3, 6, 5, 0, 4, 0, 4, 0, 5, 6, 3, 7, 0, 5, 2, 6, 1, 2, 6, 1, 0, 5, 2, 1,
    3, 7, 6, 5, 0, 4, 0, 4, 0, 5, 6, 7, 3, 1, 2, 5, 0, 1, 6, 2]
  wz := [0, 1, 2, 6, 5, 2, 7, 6, 2, 1, 5, 0, 4, 0, 4, 0, 5, 1, 2, 6, 7, 2, 5, 6, 2, 1, 0, 4, 5, 1,
    0, 6, 2, 5, 7, 2, 6, 5, 0, 4, 0, 4, 0, 5, 6, 2, 7, 5, 2, 6, 0, 1, 5, 4]
  gens :=
    [⟨[0, 2, 6, 5, 0, 2, 7, 6, 5, 2, 4, 1, 0, 1, 4, 2, 5, 6, 7, 2, 0, 5, 6, 2, 0, 2, 5, 0, 5, 2],
       false, 1, 0, 0, 1⟩,
     ⟨[2, 5, 0, 5, 2, 0, 2, 6, 5, 0, 2, 7, 6, 5, 2, 4, 1, 0, 1, 4, 2, 5, 6, 7, 2, 0, 5, 6, 2, 0],
       false, 1, 0, 0, 1⟩,
     ⟨[0, 4, 5, 4, 6, 7, 3, 2, 5, 4, 6, 1, 3, 2, 3, 1, 6, 4, 5, 2, 3, 7, 6, 4, 5, 4, 0, 3, 2, 3],
       false, 1, 1, 0, 2⟩,
     ⟨[3, 2, 3, 0, 4, 5, 4, 6, 7, 3, 2, 5, 4, 6, 1, 3, 2, 3, 1, 6, 4, 5, 2, 3, 7, 6, 4, 5, 4, 0],
       false, 1, 1, 0, 2⟩,
     ⟨[6, 5, 0, 2, 3, 4, 6, 5, 2, 7, 6, 2, 6, 7, 2, 5, 6, 4, 3, 2, 0, 5, 6, 5, 2, 6, 2, 6, 2, 5],
       false, 2, 0, 1, 1⟩,
     ⟨[5, 2, 6, 2, 6, 2, 5, 6, 5, 0, 2, 3, 4, 6, 5, 2, 7, 6, 2, 6, 7, 2, 5, 6, 4, 3, 2, 0, 5, 6],
       false, 2, 0, 1, 1⟩,
     ⟨[2, 6, 5, 2, 7, 6, 1, 2, 1, 6, 7, 2, 5, 3, 5, 7, 2, 6, 5, 4, 0, 4, 5, 6, 2, 7, 5, 3, 6, 2],
       false, 1, 0, 2, 2⟩,
     ⟨[2, 6, 3, 5, 7, 2, 6, 5, 4, 0, 4, 5, 6, 2, 7, 5, 3, 5, 2, 7, 6, 1, 2, 1, 6, 7, 2, 5, 6, 2],
       false, 1, 0, 2, 2⟩,
     ⟨[0, 2, 4, 1, 5, 6, 5, 7, 6, 5, 4, 0, 4, 5, 6, 7, 5, 6, 5, 1, 4, 2, 6, 2, 5, 0, 4, 0, 4, 0, 5,
       2, 6, 0], false, 1, 0, 0, 1⟩,
     ⟨[0, 6, 2, 5, 0, 4, 0, 4, 0, 5, 2, 6, 2, 4, 1, 5, 6, 5, 7, 6, 5, 4, 0, 4, 5, 6, 7, 5, 6, 5, 1,
       4, 2, 0], false, 1, 0, 0, 1⟩,
     ⟨[2, 5, 0, 2, 4, 6, 5, 7, 6, 1, 2, 1, 6, 7, 5, 6, 4, 2, 0, 5, 6, 5, 0, 2, 4, 5, 0, 5, 4, 2, 0,
       5, 6, 2], false, 2, 0, 0, 2⟩,
     ⟨[2, 6, 5, 0, 2, 4, 5, 0, 5, 4, 2, 0, 5, 6, 5, 0, 2, 4, 6, 5, 7, 6, 1, 2, 1, 6, 7, 5, 6, 4, 2,
       0, 5, 2], false, 2, 0, 0, 2⟩,
     ⟨[1, 2, 6, 3, 2, 5, 0, 2, 7, 6, 1, 2, 1, 6, 7, 2, 0, 5, 2, 3, 6, 2, 1, 2, 5, 0, 4, 7, 2, 5, 0,
       5, 2, 7, 4, 0, 5, 2], false, 2, 0, 0, 2⟩,
     ⟨[2, 5, 0, 4, 7, 2, 5, 0, 5, 2, 7, 4, 0, 5, 2, 1, 2, 6, 3, 2, 5, 0, 2, 7, 6, 1, 2, 1, 6, 7, 2,
       0, 5, 2, 3, 6, 2, 1], false, 2, 0, 0, 2⟩,
     ⟨[5, 6, 1, 5, 7, 2, 6, 5, 0, 4, 0, 4, 0, 5, 6, 2, 7, 5, 1, 6, 5, 0, 5, 4, 6, 1, 3, 6, 5, 0, 5,
       6, 3, 1, 6, 4, 5, 0], false, 1, 0, 0, 1⟩,
     ⟨[0, 5, 4, 6, 1, 3, 6, 5, 0, 5, 6, 3, 1, 6, 4, 5, 0, 5, 6, 1, 5, 7, 2, 6, 5, 0, 4, 0, 4, 0, 5,
       6, 2, 7, 5, 1, 6, 5], false, 1, 0, 0, 1⟩,
     ⟨[7, 6, 5, 2, 3, 4, 5, 6, 1, 0, 1, 6, 5, 4, 3, 2, 5, 6, 7, 6, 2, 5, 7, 6, 5, 0, 4, 0, 4, 0, 5,
       6, 7, 5, 2, 6], true, 2, 0, 2, 1⟩,
     ⟨[6, 2, 5, 7, 6, 5, 0, 4, 0, 4, 0, 5, 6, 7, 5, 2, 6, 7, 6, 5, 2, 3, 4, 5, 6, 1, 0, 1, 6, 5, 4,
       3, 2, 5, 6, 7], true, 2, 0, 2, 1⟩,
     ⟨[3, 7, 6, 5, 0, 2, 1, 3, 2, 3, 1, 2, 0, 5, 6, 7, 5, 1, 7, 2, 3, 6, 5, 0, 4, 0, 4, 0, 5, 6, 3,
       2, 7, 1, 5, 3], true, 2, 0, 0, 2⟩,
     ⟨[3, 5, 1, 7, 2, 3, 6, 5, 0, 4, 0, 4, 0, 5, 6, 3, 2, 7, 1, 5, 7, 6, 5, 0, 2, 1, 3, 2, 3, 1, 2,
       0, 5, 6, 7, 3], true, 2, 0, 0, 2⟩,
     ⟨[0, 1, 5, 4, 6, 2, 1, 5, 7, 2, 6, 2, 6, 2, 7, 5, 1, 2, 6, 4, 5, 1, 0, 2, 4, 6, 5, 7, 2, 6, 2,
       6, 2, 7, 5, 6, 4, 2], true, 1, 0, 0, 1⟩,
     ⟨[2, 4, 6, 5, 7, 2, 6, 2, 6, 2, 7, 5, 6, 4, 2, 0, 1, 5, 4, 6, 2, 1, 5, 7, 2, 6, 2, 6, 2, 7, 5,
       1, 2, 6, 4, 5, 1, 0], true, 1, 0, 0, 1⟩,
     ⟨[2, 4, 6, 2, 1, 5, 7, 2, 6, 2, 6, 2, 7, 5, 1, 2, 6, 4, 2, 1, 3, 4, 6, 5, 4, 6, 1, 3, 2, 3, 1,
       6, 4, 5, 6, 4, 3, 1], true, 1, 0, 0, 1⟩,
     ⟨[1, 3, 4, 6, 5, 4, 6, 1, 3, 2, 3, 1, 6, 4, 5, 6, 4, 3, 1, 2, 4, 6, 2, 1, 5, 7, 2, 6, 2, 6, 2,
       7, 5, 1, 2, 6, 4, 2], true, 1, 0, 0, 1⟩,
     ⟨[1, 3, 4, 6, 5, 4, 6, 1, 3, 2, 3, 1, 6, 4, 5, 6, 4, 3, 1, 2, 4, 6, 2, 1, 5, 7, 2, 6, 2, 6, 2,
       7, 5, 1, 2, 6, 4, 2], true, 1, 0, 0, 1⟩,
     ⟨[2, 4, 6, 2, 1, 5, 7, 2, 6, 2, 6, 2, 7, 5, 1, 2, 6, 4, 2, 1, 3, 4, 6, 5, 4, 6, 1, 3, 2, 3, 1,
       6, 4, 5, 6, 4, 3, 1], true, 1, 0, 0, 1⟩,
     ⟨[2, 6, 5, 0, 2, 7, 6, 5, 2, 4, 1, 0, 1, 4, 2, 5, 6, 7, 2, 0, 5, 6, 2], false, 1, 0, 0, 1⟩,
     ⟨[0, 3, 5, 0, 2, 6, 5, 7, 6, 1, 5, 4, 0, 4, 5, 1, 6, 7, 5, 6, 2, 0, 5, 3, 0],
       false, 1, 0, 0, 1⟩,
     ⟨[1, 4, 5, 2, 6, 1, 2, 5, 7, 6, 1, 5, 0, 4, 0, 4, 0, 5, 1, 6, 7, 5, 2, 1, 6, 2, 5, 4, 1],
       false, 1, 0, 0, 1⟩,
     ⟨[1, 6, 2, 5, 0, 7, 3, 6, 5, 0, 4, 0, 4, 0, 5, 6, 3, 7, 0, 5, 2, 6, 1], true, 2, 0, 2, 1⟩,
     ⟨[0, 3, 4, 5, 4, 6, 2, 5, 2, 4, 7, 6, 1, 2, 1, 6, 7, 4, 2, 5, 2, 6, 4, 5, 4, 3, 0],
       false, 1, 1, 0, 2⟩,
     ⟨[0, 7, 6, 5, 0, 2, 4, 6, 3, 5, 2, 7, 6, 2, 6, 7, 2, 5, 3, 6, 4, 2, 0, 5, 6, 7, 0],
       false, 1, 1, 0, 2⟩,
     ⟨[3, 4, 6, 1, 2, 5, 4, 6, 2, 5, 7, 2, 6, 2, 6, 2, 7, 5, 2, 6, 4, 5, 2, 1, 6, 4, 3],
       true, 1, 0, 0, 1⟩,
     ⟨[2, 5, 0, 7, 3, 6, 5, 2, 4, 6, 5, 7, 3, 6, 1, 2, 1, 6, 3, 7, 5, 6, 4, 2, 5, 6, 3, 7, 0, 5, 2],
       true, 1, 0, 0, 1⟩,
     ⟨[6, 3, 5, 7, 2, 6, 1, 5, 4, 6, 5, 2, 7, 6, 1, 2, 1, 6, 7, 2, 5, 6, 4, 5, 1, 6, 2, 7, 5, 3, 6],
       true, 1, 0, 0, 1⟩,
     ⟨[0, 3, 4, 1, 7, 2, 3, 6, 5, 4, 6, 2, 5, 7, 2, 6, 2, 6, 2, 7, 5, 2, 6, 4, 5, 6, 3, 2, 7, 1, 4,
       3, 0], true, 1, 0, 0, 1⟩]
  targets :=
    [[0, 8, 20, 10, 22, 28, 23, 11, 21, 9, 1],
     [14, 35, 12, 20, 26, 21, 13, 35, 15],
     [10, 24, 30, 25, 11],
     [10, 12, 18, 6, 34, 7, 19, 13, 11],
     [12, 32, 10, 18, 27, 19, 11, 32, 13],
     [12, 20, 16, 6, 29, 7, 17, 21, 13],
     [4, 33, 14, 18, 14, 35, 15, 19, 15, 33, 5],
     [2, 6, 22, 14, 24, 31, 25, 15, 23, 7, 3]]

@[expose] def F4TwoThreePlanesCheck : Prop :=
  f4ThreePlanes.check = true

end CFSG.LocalAnalysis.RankThreeTheoremC.F4TwoPlanes
