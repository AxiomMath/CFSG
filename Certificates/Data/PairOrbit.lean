module

public import Certificates.Data.PtOrbit
public meta import Certificates.Data.PtOrbit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.PairOrbit

open CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Solomon.Coordinator.PtOrbit

@[inline, expose] def pairImg (n : Nat) (g : Table) (c : Nat) : Nat := ap g (c / n) * n + ap g (c % n)

def pairBFS (n : Nat) (G : Array Table) (c0 cap : Nat) : PTree :=
  Id.run do
    let mut pts : Array Nat := #[c0]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut seen : Std.HashSet Nat := (Std.HashSet.emptyWithCapacity 1).insert c0
    let mut h := 0
    while h < pts.size && pts.size < cap do
      for l in [0:G.size] do
        let y := pairImg n G[l]! pts[h]!
        if !seen.contains y then
          seen := seen.insert y
          pts := pts.push y
          par := par.push h
          lab := lab.push l
      h := h + 1
    return ⟨pts, par, lab⟩

@[expose] def pairOK (n : Nat) (G : Array Table) (c0 : Nat) (T : PTree) : Bool :=
  decide (0 < T.pts.size) && T.par.size == T.pts.size && T.lab.size == T.pts.size &&
    T.pts[0]! == c0 &&
    allIn 0 T.pts.size (fun i => decide (T.pts[i]! < n * n) &&
      (i == 0 || (decide (T.par[i]! < i) && decide (T.lab[i]! < G.size) &&
        T.pts[i]! == pairImg n G[T.lab[i]!]! T.pts[T.par[i]!]!))) &&
    CFSG.Sporadic.Co1.InvNative.distinctKeys T.pts.toList &&
    (let ks : Std.HashSet Nat := Std.HashSet.ofList T.pts.toList
     allIn 0 T.pts.size fun i => allIn 0 G.size fun l => ks.contains (pairImg n G[l]! T.pts[i]!))

end CFSG.HardMathSupport.Solomon.Coordinator.PairOrbit
