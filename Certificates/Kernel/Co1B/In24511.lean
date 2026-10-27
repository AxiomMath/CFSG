module

public import Certificates.Kernel.Co1B.In24513
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs

public section

namespace CertificateChecks.KernelCo1B.H24511

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.InvNative CFSG.EvenSporadicStandard.TwoCo1.HypOne
  CertificateChecks.KernelCo1B.Syl2B

def packRows (x : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => acc ||| (x[i]?.getD 0 <<< (24 * i))) 0

def code (cg ci : Array Rows) (p : Rows) : Nat :=
  let c := conjBFS cg ci p 5
  let w := (List.range cg.size).map fun l =>
    (c.pts.findIdx? (· == conjRows cg[l]! ci[l]! p)).getD 15
  let pk := c.pts.map packRows
  let s := (Array.range c.pts.size).qsort fun a b => pk[a]! < pk[b]!
  let fields := c.lab.toList.take 6 ++ w ++ s.toList
  (List.range fields.length).foldl (fun acc j => acc ||| (fields[j]! <<< (4 * j))) 0

def codes24511 : List Nat :=
  let cg : Array Rows := (brayElts (brayRows aR twoBD1) twoBBray).toArray
  let ci := cg.map inv
  ((gtBFS sgArr 32769).pts.map fun p => if fourRows p then code cg ci p else 0).toList

end CertificateChecks.KernelCo1B.H24511

end
