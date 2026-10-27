module

public import CFSG.LieType.Simplicity.TitsBits

public section

namespace CFSG.RankThree.PartOne.SEITZX

open CFSG.LieType.Simplicity.TitsBits

@[expose] def letterOfCode (c : ℕ) : Letter :=
  if h : c < 4 then .x ⟨c, h⟩ else .n ⟨(c - 4) % 4, Nat.mod_lt _ (by norm_num)⟩

@[expose] def wordOfCodes (w : List ℕ) : List Letter :=
  w.map letterOfCode

@[expose] def codeBits (w : List ℕ) : ℕ :=
  evalB (wordOfCodes w)

@[expose] def matPowB (A : ℕ) : ℕ → ℕ
  | 0 => oneBits
  | n + 1 => mul A (matPowB A n)

@[expose] def targetWord (t : ℕ) : List ℕ :=
  if t < 4 then [t] else [t - 4, t, t - 4]

structure PlaneCert where
  p : ℕ
  wa : List ℕ
  wb : List ℕ
  gens : List (List ℕ × ℕ × ℕ)
  targets : List (List ℕ)

@[expose] def PlaneCert.prodBits (c : PlaneCert) (idxs : List ℕ) : ℕ :=
  (idxs.map fun k => codeBits (c.gens.getD k ([], 0, 0)).1).foldr (fun S acc => mul S acc) oneBits

@[expose] def PlaneCert.elemBits (c : PlaneCert) (i j : ℕ) : ℕ :=
  mul (matPowB (codeBits c.wa) i) (matPowB (codeBits c.wb) j)

@[expose] def PlaneCert.check (c : PlaneCert) : Bool :=
  decide (matPowB (codeBits c.wa) c.p % 2 ^ 2704 = oneBits % 2 ^ 2704) &&
  decide (matPowB (codeBits c.wb) c.p % 2 ^ 2704 = oneBits % 2 ^ 2704) &&
  decide (mul (codeBits c.wa) (codeBits c.wb) % 2 ^ 2704 =
    mul (codeBits c.wb) (codeBits c.wa) % 2 ^ 2704) &&
  decide (codeBits c.wa % 2 ^ 2704 ≠ oneBits % 2 ^ 2704) &&
  (List.range c.p).all (fun j =>
    decide (matPowB (codeBits c.wa) j % 2 ^ 2704 ≠ codeBits c.wb % 2 ^ 2704)) &&
  c.gens.all (fun g =>
    decide (c.elemBits g.2.1 g.2.2 % 2 ^ 2704 ≠ oneBits % 2 ^ 2704) &&
    decide (mul (codeBits g.1) (c.elemBits g.2.1 g.2.2) % 2 ^ 2704 =
      mul (c.elemBits g.2.1 g.2.2) (codeBits g.1) % 2 ^ 2704)) &&
  (List.range 8).all (fun t =>
    decide (c.prodBits (c.targets.getD t []) % 2 ^ 2704 = codeBits (targetWord t) % 2 ^ 2704))

@[expose] def cert5 : PlaneCert where
  p := 5
  wa := [5, 6, 5, 0, 2, 5, 0, 1]
  wb := [4, 5, 2, 5, 4, 7, 6, 4, 5, 4, 0, 4, 5, 4, 6, 7, 0, 4, 5, 6, 1, 2, 1, 6, 5, 4, 0, 6, 7, 1, 6, 0, 4, 5, 0, 5, 4, 0, 6, 1, 7, 6]
  gens :=
    [([6, 4, 1, 5, 4, 0, 4, 5, 1, 4, 6], 0, 1),
    ([3, 7, 5, 6, 4, 5, 6, 4, 3, 1, 2, 5, 0, 5, 2, 1, 3, 4, 6, 5, 4, 6, 5, 7, 3], 1, 1),
    ([6, 0, 4, 0, 5, 6, 2, 7, 5, 2, 1, 6, 0, 1, 5, 4, 0, 4, 5, 1, 0, 6, 1, 2, 5, 7, 2, 6, 5, 0, 4, 0, 6], 1, 1),
    ([2], 0, 1),
    ([0, 5, 2, 5, 0], 0, 1),
    ([4, 5, 2, 5, 4], 1, 0),
    ([0, 5, 2, 6, 2, 6, 2, 5, 0], 0, 1),
    ([7, 6, 5, 1, 6, 7, 4, 5, 2, 6, 2, 6, 2, 5, 4, 7, 6, 1, 5, 6, 7], 1, 0),
    ([7, 6, 1, 5, 6, 7, 0, 4, 5, 2, 6, 1, 2, 1, 6, 2, 5, 4, 0, 7, 6, 5, 1, 6, 7], 1, 0)]
  targets :=
    [[2, 4, 1, 4, 2, 7, 1, 0, 1, 7, 2, 4, 1, 4, 2],
    [0, 3, 6, 1, 0, 1, 3, 0, 3, 1, 0, 1, 6, 3, 0],
    [2, 8, 2, 3, 2, 5, 8, 5, 8, 5, 2, 3, 2, 8, 2],
    [4, 5, 2, 1, 4, 2, 5, 2, 4, 1, 2, 5, 4],
    [0, 6, 4, 1, 6, 2, 6, 0, 6, 2, 6, 1, 4, 6, 0],
    [4, 0, 6, 0, 4, 3, 0, 3, 4, 0, 6, 0, 4],
    [2, 6, 2, 0, 6, 0, 2, 5, 2, 0, 6, 0, 2, 6, 2],
    [1, 5, 1, 2, 3, 2, 5, 2, 3, 2, 1, 5, 1]]

@[expose] def cert7 : PlaneCert where
  p := 7
  wa := [3, 4, 3, 6, 5, 1, 2, 6]
  wb := [7, 6, 2, 6, 7, 1, 2, 7, 0, 1, 2, 1, 0, 7, 2, 1, 7, 6, 5, 6, 7, 4, 5, 2, 6, 2, 6, 2, 5, 4, 7, 6, 5, 6, 7]
  gens :=
    [([4, 2, 1, 0, 1, 2, 4], 0, 1),
    ([5, 2, 5, 0, 5, 2, 5], 0, 1),
    ([4, 5, 2, 1, 0, 1, 2, 5, 4], 0, 1),
    ([6, 5, 0, 4, 1, 0, 1, 4, 0, 5, 6], 0, 1),
    ([1, 6, 2, 5, 0, 4, 0, 4, 0, 5, 2, 6, 1], 0, 1),
    ([6, 5, 4, 1, 2, 5, 0, 5, 2, 1, 4, 5, 6], 0, 1),
    ([1, 2, 7, 0, 1, 2, 1, 0, 7, 2, 1], 1, 0),
    ([5, 6, 7, 4, 5, 2, 5, 4, 7, 6, 5], 1, 0),
    ([1, 2, 6, 5, 6, 7, 5, 6, 4, 5, 6, 2, 3, 0, 1, 2, 1, 0, 3, 2, 6, 5, 4, 6, 5, 7, 6, 5, 6, 2, 1], 1, 4)]
  targets :=
    [[0, 8, 2, 5, 0, 5, 6, 8, 4, 8, 6, 5, 0, 5, 2, 8, 0],
    [3, 2, 5, 6, 8, 4, 8, 2, 4, 2, 8, 4, 8, 6, 5, 2, 3],
    [5, 6, 8, 1, 8, 2, 5, 8, 4, 8, 7, 8, 4, 8, 5, 2, 8, 1, 8, 6, 5],
    [2, 0, 1, 8, 4, 8, 6, 7, 6, 8, 4, 8, 1, 0, 2],
    [5, 4, 8, 2, 0, 5, 6, 8, 4, 8, 6, 5, 0, 2, 8, 4, 5],
    [0, 8, 4, 8, 5, 2, 5, 4, 5, 2, 5, 8, 4, 8, 0],
    [8, 2, 1, 0, 5, 8, 6, 1, 8, 7, 8, 1, 6, 8, 5, 0, 1, 2, 8],
    [5, 8, 1, 8, 7, 8, 1, 8, 5]]

@[expose] def F4TwoSeitzCheck : Prop :=
  cert5.check = true ∧ cert7.check = true

end CFSG.RankThree.PartOne.SEITZX
