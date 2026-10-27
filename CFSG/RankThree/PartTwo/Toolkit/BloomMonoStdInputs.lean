module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
public import CFSG.RankThree.PartTwo.Toolkit.RawGL
public import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public import CFSG.RankThree.PartTwo.Toolkit.PermTab
public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.RankThree.PartTwo.Toolkit.BloomMonoTrees
public meta import CFSG.RankThree.PartTwo.Toolkit.RawGL
public meta import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public meta import CFSG.RankThree.PartTwo.Toolkit.PermTab
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Toolkit.RawTree

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Raw Subgroup CFSG.RankThree.SubgroupLists

open scoped Matrix

@[expose] def colV (M : R9) : ℕ → V3
  | 0 => ⟨M.a, M.d, M.g⟩
  | 1 => ⟨M.b, M.e, M.h⟩
  | _ => ⟨M.c, M.f, M.i⟩

@[expose] def unitV : ℕ → V3
  | 0 => ⟨1, 0, 0⟩
  | 1 => ⟨0, 1, 0⟩
  | _ => ⟨0, 0, 1⟩

@[expose] def vsmulR (a : ZMod 3) (v : V3) : V3 := ⟨a * v.x, a * v.y, a * v.z⟩

@[expose] def inSpanR (u w : V3) : Bool := vals.any fun a => u == vsmulR a w

@[expose] def monRaw : List R9 :=
  [⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 1⟩,
  ⟨1, 0, 0, 0, 2, 0, 0, 0, 2⟩, ⟨2, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨2, 0, 0, 0, 1, 0, 0, 0, 2⟩,
  ⟨2, 0, 0, 0, 2, 0, 0, 0, 1⟩, ⟨2, 0, 0, 0, 2, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 0, 1, 0, 1, 0⟩,
  ⟨1, 0, 0, 0, 0, 2, 0, 1, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 2, 0⟩, ⟨1, 0, 0, 0, 0, 2, 0, 2, 0⟩,
  ⟨2, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨2, 0, 0, 0, 0, 2, 0, 1, 0⟩, ⟨2, 0, 0, 0, 0, 1, 0, 2, 0⟩,
  ⟨2, 0, 0, 0, 0, 2, 0, 2, 0⟩, ⟨0, 1, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 0, 1, 0, 0, 0, 0, 2⟩,
  ⟨0, 2, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 2, 0, 1, 0, 0, 0, 0, 2⟩, ⟨0, 1, 0, 2, 0, 0, 0, 0, 1⟩,
  ⟨0, 1, 0, 2, 0, 0, 0, 0, 2⟩, ⟨0, 2, 0, 2, 0, 0, 0, 0, 1⟩, ⟨0, 2, 0, 2, 0, 0, 0, 0, 2⟩,
  ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 2, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 2, 0⟩,
  ⟨0, 0, 2, 1, 0, 0, 0, 2, 0⟩, ⟨0, 0, 1, 2, 0, 0, 0, 1, 0⟩, ⟨0, 0, 2, 2, 0, 0, 0, 1, 0⟩,
  ⟨0, 0, 1, 2, 0, 0, 0, 2, 0⟩, ⟨0, 0, 2, 2, 0, 0, 0, 2, 0⟩, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩,
  ⟨0, 1, 0, 0, 0, 2, 1, 0, 0⟩, ⟨0, 2, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 2, 0, 0, 0, 2, 1, 0, 0⟩,
  ⟨0, 1, 0, 0, 0, 1, 2, 0, 0⟩, ⟨0, 1, 0, 0, 0, 2, 2, 0, 0⟩, ⟨0, 2, 0, 0, 0, 1, 2, 0, 0⟩,
  ⟨0, 2, 0, 0, 0, 2, 2, 0, 0⟩, ⟨0, 0, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 2, 0, 1, 0, 1, 0, 0⟩,
  ⟨0, 0, 1, 0, 2, 0, 1, 0, 0⟩, ⟨0, 0, 2, 0, 2, 0, 1, 0, 0⟩, ⟨0, 0, 1, 0, 1, 0, 2, 0, 0⟩,
  ⟨0, 0, 2, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 1, 0, 2, 0, 2, 0, 0⟩, ⟨0, 0, 2, 0, 2, 0, 2, 0, 0⟩]

@[expose] def n0Raw : List R9 :=
  [⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 2⟩, ⟨2, 0, 0, 0, 1, 0, 0, 0, 2⟩,
  ⟨2, 0, 0, 0, 2, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 0, 2, 0, 1, 0⟩, ⟨1, 0, 0, 0, 0, 1, 0, 2, 0⟩,
  ⟨2, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨2, 0, 0, 0, 0, 2, 0, 2, 0⟩, ⟨0, 1, 0, 1, 0, 0, 0, 0, 2⟩,
  ⟨0, 2, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 1, 0, 2, 0, 0, 0, 0, 1⟩, ⟨0, 2, 0, 2, 0, 0, 0, 0, 2⟩,
  ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 2, 1, 0, 0, 0, 2, 0⟩, ⟨0, 0, 2, 2, 0, 0, 0, 1, 0⟩,
  ⟨0, 0, 1, 2, 0, 0, 0, 2, 0⟩, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 2, 0, 0, 0, 2, 1, 0, 0⟩,
  ⟨0, 1, 0, 0, 0, 2, 2, 0, 0⟩, ⟨0, 2, 0, 0, 0, 1, 2, 0, 0⟩, ⟨0, 0, 2, 0, 1, 0, 1, 0, 0⟩,
  ⟨0, 0, 1, 0, 2, 0, 1, 0, 0⟩, ⟨0, 0, 1, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 2, 0, 2, 0, 2, 0, 0⟩]

@[expose] def g0Raw : List R9 :=
  [⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 2⟩, ⟨2, 0, 0, 0, 1, 0, 0, 0, 2⟩,
  ⟨2, 0, 0, 0, 2, 0, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 2, 1, 0, 0, 0, 2, 0⟩,
  ⟨0, 0, 2, 2, 0, 0, 0, 1, 0⟩, ⟨0, 0, 1, 2, 0, 0, 0, 2, 0⟩, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩,
  ⟨0, 2, 0, 0, 0, 2, 1, 0, 0⟩, ⟨0, 1, 0, 0, 0, 2, 2, 0, 0⟩, ⟨0, 2, 0, 0, 0, 1, 2, 0, 0⟩]

@[expose] def c3Raw : List R9 :=
  [⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 2, 1, 0, 0, 0, 2, 0⟩, ⟨0, 0, 2, 2, 0, 0, 0, 1, 0⟩,
  ⟨0, 0, 1, 2, 0, 0, 0, 2, 0⟩, ⟨0, 1, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 2, 0, 0, 0, 2, 1, 0, 0⟩,
  ⟨0, 1, 0, 0, 0, 2, 2, 0, 0⟩, ⟨0, 2, 0, 0, 0, 1, 2, 0, 0⟩]

@[expose] def diagR : List V3 := [⟨1, 1, 1⟩, ⟨1, 2, 2⟩, ⟨2, 1, 2⟩, ⟨2, 2, 1⟩]

@[expose] def diagIdx (u : V3) : ℕ :=
  ((List.range 4).find? fun j => inSpanR u (diagR.getD j vzero)).getD 0

@[expose] def psiTabR (M : R9) : List ℕ := diagR.map fun d => diagIdx (rmv M d)

@[expose] def fixVecR (c : R9) : V3 :=
  (allV3.find? fun v => v != vzero && rmv c v == v).getD vzero

@[expose] def negR : R9 := ⟨2, 0, 0, 0, 2, 0, 0, 0, 2⟩

@[expose] def isMonColR (v : V3) : Bool :=
  v != vzero && ((List.range 3).any fun j => inSpanR v (unitV j))

@[expose] def monCol3 (a b d : ℕ) : Bool :=
  (a != 0 && b == 0 && d == 0) || (a == 0 && b != 0 && d == 0) || (a == 0 && b == 0 && d != 0)

@[expose] def mono1At (M c : ℕ) : Bool :=
  !(monCol3 (dg c 1) (dg c 27) (dg c 729) && monCol3 (dg c 3) (dg c 81) (dg c 2187) &&
    monCol3 (dg c 9) (dg c 243) (dg c 6561)) || ndet c == 0 || M.testBit c

@[expose] def mc1 : Bool :=
  (List.range 19683).all (mono1At (codeMask (monRaw.map code)))

@[expose] def mc2 : Bool :=
  monRaw.all fun M => ((List.range 3).all fun i => isMonColR (colV M i)) && rdet M != 0 &&
    monRaw.any fun N => rmul M N == rone

@[expose] def mc3 : Bool :=
  (monRaw.all fun M => rdet M != 1 || n0Raw.contains M) &&
    (n0Raw.all fun M => monRaw.contains M && rdet M == 1) && decide n0Raw.Nodup &&
    n0Raw.length == 24

@[expose] def mc4 : Bool :=
  (n0Raw.all fun A => n0Raw.all fun B =>
    toP4 (psiTabR (rmul A B)) == toP4 (psiTabR A) * toP4 (psiTabR B)) &&
  (n0Raw.all fun A => n0Raw.all fun B => toP4 (psiTabR A) != toP4 (psiTabR B) || A == B) &&
  (n0Raw.all fun M => decide (Equiv.Perm.sign (toP4 (psiTabR M)) = 1) == g0Raw.contains M) &&
  (g0Raw.all fun M => n0Raw.contains M)

@[expose] def mc5 : Bool := monRaw.all fun M => n0Raw.contains M || n0Raw.contains (rmul negR M)

@[expose] def mc6 : Bool :=
  monRaw.all fun M₁ => monRaw.all fun M₂ => !inSpanR (colV M₁ 0) (unitV 1) ||
    !inSpanR (colV M₂ 0) (unitV 2) || c3Raw.contains (rpowR M₁ 4) ||
    c3Raw.contains (rpowR M₂ 4) || c3Raw.contains (rpowR (rmul M₁ M₂) 4)

@[expose] def mono7At (i j : ℕ) : Bool :=
  let c := c3Raw.getD i rone
  let h := monRaw.getD j rone
  let t := mono7Trees.getD (48 * i + j) (0, 0, 0, 0)
  inSpanR (rmv h (fixVecR c)) (fixVecR c) ||
    (treeOKP [code c, code h] t.1 t.2.1 t.2.2.1 t.2.2.2 &&
      g0Raw.all fun g => (treeMask t.1 t.2.2.2).testBit (code g))

@[expose] def mc7 : Bool :=
  (c3Raw.all fun c => fixVecR c != vzero && rmv c (fixVecR c) == fixVecR c) &&
  c3Raw.length == 8 && monRaw.length == 48 &&
  (List.range 8).all fun i => (List.range 48).all fun j => mono7At i j

@[expose] def monoCheck : Bool := mc1 && mc2 && mc3 && mc4 && mc5 && mc6 && mc7

end CFSG.RankThree.PartTwo.Toolkit
