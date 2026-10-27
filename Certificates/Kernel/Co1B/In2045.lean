module

public import CFSG.Sporadic.Co1Block.CentCheck
public import CFSG.Sporadic.Co1Block.TwoBData

public section

namespace CertificateChecks.KernelCo1B.Cent2045

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native

def dag₁ : List Rows × List Rows × Bool := brayRows aR twoBD1

def dag₂ : List Rows × List Rows × Bool := dag (brayElts dag₁ twoBBray) twoBD2

def lvB0 : List Nat := [twoBVBase.getD 0 0]
def lvG0 : List (List Nat) := [twoBVGens.getD 0 []]
def lvS0 : List Nat := [twoBVSizes.getD 0 0]
def lvB1 : List Nat := [twoBVBase.getD 1 0]
def lvG1 : List (List Nat) := [twoBVGens.getD 1 []]
def lvS1 : List Nat := [twoBVSizes.getD 1 0]
def lvB2 : List Nat := [twoBVBase.getD 2 0]
def lvG2 : List (List Nat) := [twoBVGens.getD 2 []]
def lvS2 : List Nat := [twoBVSizes.getD 2 0]
def lvB3 : List Nat := [twoBVBase.getD 3 0]
def lvG3 : List (List Nat) := [twoBVGens.getD 3 []]
def lvS3 : List Nat := [twoBVSizes.getD 3 0]

end CertificateChecks.KernelCo1B.Cent2045

end
