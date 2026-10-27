module

public import Certificates.Data.CFSGNative.Co1.Involutions
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.Co1.TwoBNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Co1.InvNative

structure GTree where
  pts : Array (Array Nat)
  par : Array Nat
  lab : Array Nat
deriving Inhabited

@[expose] def gtPointOK (G : Array (Array Nat)) (T : GTree) (i : Nat) : Bool :=
  validRows T.pts[i]! &&
    (if i == 0 then T.pts[i]! == idRows 24
     else decide (T.par[i]! < i) && decide (T.lab[i]! < G.size) &&
       T.pts[i]! == mulRows 24 T.pts[T.par[i]!]! G[T.lab[i]!]!)

@[expose] def gtClosed (G : Array (Array Nat)) (T : GTree) : Bool :=
  let ks : Std.HashSet (Array Nat) := Std.HashSet.ofList T.pts.toList
  allIn 0 T.pts.size fun i => allIn 0 G.size fun l => ks.contains (mulRows 24 T.pts[i]! G[l]!)

@[expose] def gtOK (G : Array (Array Nat)) (T : GTree) : Bool :=
  decide (0 < T.pts.size) && T.par.size == T.pts.size && T.lab.size == T.pts.size &&
    allIn 0 T.pts.size (gtPointOK G T) && distinctKeys (T.pts.toList.map rowsKey) && gtClosed G T

def gtBFS (G : Array (Array Nat)) (cap : Nat) : GTree :=
  Id.run do
    let root := idRows 24
    let mut pts : Array (Array Nat) := #[root]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut seen : Std.HashSet (Array Nat) := ({} : Std.HashSet (Array Nat)).insert root
    let mut h := 0
    while h < pts.size && pts.size < cap do
      for l in [0:G.size] do
        let y := mulRows 24 pts[h]! G[l]!
        if !seen.contains y then
          seen := seen.insert y
          pts := pts.push y
          par := par.push h
          lab := lab.push l
      h := h + 1
    return ⟨pts, par, lab⟩

@[expose] def gtInterCount (T : GTree) (g gi : Array Nat) : Nat :=
  let ks : Std.HashSet (Array Nat) := Std.HashSet.ofList T.pts.toList
  countBelow (fun i => ks.contains (conjRows gi g T.pts[i]!)) T.pts.size 0

end CFSG.Sporadic.Co1.TwoBNative
