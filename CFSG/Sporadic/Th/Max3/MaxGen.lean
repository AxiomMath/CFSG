module

public import Certificates.Data.CFSGNative.Th.Certificate

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.Th.Native

@[expose] def treeTable (n : Nat) (pl : Table) (gens : Nat → Table) (k : Nat) : Table :=
  if _h : 0 < k ∧ treePar (pl[k]!).toNat < k then
    compT n (gens (treeLab (pl[k]!).toNat)) (treeTable n pl gens (treePar (pl[k]!).toNat))
  else idT n
termination_by k

@[expose] def schreierTable (n : Nat) (pts pl pos : Table) (g1 g2 : Table) (k l : Nat) :
    Table × Bool :=
  let gl := letters g1 g2 l
  let j := ap pos (ap gl (ap pts k))
  let Rj := treeTable n pl (letters g1 g2) j
  let Rji := invT n Rj
  (compT n Rji (compT n gl (treeTable n pl (letters g1 g2) k)), invOK n Rj Rji)

@[expose] def countFixAux (T : Table) : Nat → Nat → Nat
  | 0, c => c
  | k + 1, c => countFixAux T k (if ap T k == k then c + 1 else c)

@[expose] def countFix (n : Nat) (T : Table) : Nat := countFixAux T n 0

@[expose] def hTreeData : String := include_str "../../../Blueprint/Data/th-H-involution-trees.txt"

@[expose] def textNats (s : String) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for line in s.splitOn "\n" do
    if line.startsWith "#" then continue
    let mut cur : Option Nat := none
    for c in line.toList do
      if '0' ≤ c && c ≤ '9' then
        cur := some ((cur.getD 0) * 10 + (c.toNat - '0'.toNat))
      else
        match cur with
        | some v => out := out.push v; cur := none
        | none => pure ()
    match cur with
    | some v => out := out.push v
    | none => pure ()
  return out

@[expose] def hTrees (s : String) : Array (Nat × Nat) × Array (Nat × Nat) :=
  let v := textNats s
  let s0 := v[0]!
  let s1 := v[1]!
  ((Array.range s0).map fun k => (v[2 + 2 * k]!, v[3 + 2 * k]!),
    (Array.range s1).map fun k => (v[2 + 2 * (s0 + k)]!, v[3 + 2 * (s0 + k)]!))

@[expose] def hEval (t : Array (Nat × Nat)) (R X Y Xi Yi : Table) (k q : Nat) : Nat :=
  if _h : 0 < (t[k]!).1 ∧ (t[k]!).1 - 1 < k then
    ap (letters X Y (t[k]!).2)
      (hEval t R X Y Xi Yi ((t[k]!).1 - 1) (ap (letters Xi Yi (t[k]!).2) q))
  else ap R q
termination_by k

@[expose] def hFp (t : Array (Nat × Nat)) (R X Y Xi Yi : Table) (k : Nat) : Nat :=
  hEval t R X Y Xi Yi k 1 * 4294967296 + hEval t R X Y Xi Yi k 2

@[expose] def hFp2 (t₀ t₁ : Array (Nat × Nat)) (R₀ R₁ X Y Xi Yi : Table) (k : Nat) : Nat :=
  if k < t₀.size then hFp t₀ R₀ X Y Xi Yi k else hFp t₁ R₁ X Y Xi Yi (k - t₀.size)

@[expose] def hOrder (t₀ t₁ : Array (Nat × Nat)) (R₀ R₁ X Y Xi Yi : Table) : Array Nat :=
  let fps := (Array.range (t₀.size + t₁.size)).map (hFp2 t₀ t₁ R₀ R₁ X Y Xi Yi)
  (Array.range (t₀.size + t₁.size)).qsort fun i j => fps[i]! < fps[j]!

@[expose] def hFpsIncreasing (t₀ t₁ : Array (Nat × Nat)) (R₀ R₁ X Y Xi Yi : Table) (π : Array Nat) :
    Bool :=
  allIn 1 π.size fun i =>
    hFp2 t₀ t₁ R₀ R₁ X Y Xi Yi π[i - 1]! < hFp2 t₀ t₁ R₀ R₁ X Y Xi Yi π[i]!

end CFSG.Sporadic.Th.Native
