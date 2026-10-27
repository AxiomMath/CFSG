module

public import CFSG.Sporadic.Co1Block.TwoACheckInputs

public section

namespace CertificateChecks.KernelCo1B.C2044

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native

def dag₁ : List Rows × List Rows × Bool := brayRows iotaARows twoAD1

def dag₂ : List Rows × List Rows × Bool := dag (brayElts dag₁ twoABray) twoAD2

def qArr : Array (Array Nat) := twoAQRows.toArray

def cG : List (Array (Array Nat)) :=
  (List.range twoARoots.length).map fun i => ((twoACGens.getD i []).map fun j => dag₂.1.getD j one).toArray

def cGi : List (Array (Array Nat)) := cG.map fun G => G.map inv

def cR : List (Array Nat) := twoARoots

def cS : List Nat := twoACSizes

end CertificateChecks.KernelCo1B.C2044

end
