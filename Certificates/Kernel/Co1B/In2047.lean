module

public import CFSG.Sporadic.Co1Block.TwoCCheckInputs

public section

namespace CertificateChecks.KernelCo1B.C2047

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native

def dag₁ : List Rows × List Rows × Bool := brayRows iotaCRows twoCD1

def dag₂ : List Rows × List Rows × Bool := dag (brayElts dag₁ twoCBray) twoCD2

def qArr : Array (Array Nat) := twoCQRows.toArray

def cG : List (Array (Array Nat)) :=
  (List.range twoCRoots.length).map fun i => ((twoCCGens.getD i []).map fun j => dag₂.1.getD j one).toArray

def cGi : List (Array (Array Nat)) := cG.map fun G => G.map inv

def cR : List (Array Nat) := twoCRoots

def cS : List Nat := twoCCSizes

end CertificateChecks.KernelCo1B.C2047

end
