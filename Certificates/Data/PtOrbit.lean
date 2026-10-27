module

public import Certificates.Data.CFSGNative.Th.Tables
public import Certificates.Data.CFSGNative.Co1.Involutions
public import Std.Data.HashSet
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Std.Data.HashSet

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.PtOrbit

open CFSG.Sporadic.Th.Native

structure PTree where
  pts : Array Nat
  par : Array Nat
  lab : Array Nat
deriving Inhabited

def ptBFS (n : Nat) (G : Array Table) (p0 cap : Nat) : PTree :=
  Id.run do
    let mut pts : Array Nat := #[p0]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut seen : Array Bool := (Array.replicate n false).set! p0 true
    let mut h := 0
    while h < pts.size && pts.size < cap do
      for l in [0:G.size] do
        let y := ap G[l]! pts[h]!
        if y < n && !seen[y]! then
          seen := seen.set! y true
          pts := pts.push y
          par := par.push h
          lab := lab.push l
      h := h + 1
    return ⟨pts, par, lab⟩

@[expose] def ptOK (n : Nat) (G : Array Table) (p0 : Nat) (T : PTree) : Bool :=
  decide (0 < T.pts.size) && T.par.size == T.pts.size && T.lab.size == T.pts.size &&
    T.pts[0]! == p0 &&
    allIn 0 T.pts.size (fun i => decide (T.pts[i]! < n) &&
      (i == 0 || (decide (T.par[i]! < i) && decide (T.lab[i]! < G.size) &&
        T.pts[i]! == ap G[T.lab[i]!]! T.pts[T.par[i]!]!))) &&
    CFSG.Sporadic.Co1.InvNative.distinctKeys T.pts.toList &&
    (let ks : Std.HashSet Nat := Std.HashSet.ofList T.pts.toList
     allIn 0 T.pts.size fun i => allIn 0 G.size fun l => ks.contains (ap G[l]! T.pts[i]!))

end CFSG.HardMathSupport.Solomon.Coordinator.PtOrbit
