module

public import Certificates.Kernel.Co1ThreeK.DataLeaf
public import Certificates.Kernel.Co1ThreeK.Letters
public import Certificates.Data.Kernel.Co1Three.Leaf
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1Leaf CFSG.KC.Co1F2
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

@[expose] def PW : List (List Nat) := Data.planeD ++ Data.planesD.flatten

@[expose] noncomputable def PD (k : Nat) : Nat := getL (nat_lit 0) LD.PD k

theorem kPD : (Nat.beq (lenL LD.PD) 10 && Nat.beq PW.length 10 && allN 10 (fun k =>
    lettersK 75 (PW.getD k []) && Nat.beq (PD k) (wordWK L.M L.MI (PW.getD k [])))) = true := by
  quickRfl

@[expose] noncomputable def AK : List Nat := [L.M 0, L.M 1, L.M 2, L.M 3, L.M 4, L.M 5]

@[expose] noncomputable def GE (ℓ : Nat) : List Nat := (LD.EV.getD ℓ []).map (eltWK AK)

@[expose] noncomputable def GD (a b : Nat) : List Nat :=
  [R.M 2, eltWK [PD 0, PD 1] (LD.DV.getD a []),
    eltWK [PD (2 + 2 * a), PD (3 + 2 * a)] (LD.DV.getD b [])]

end CertificateChecks.KernelCo1ThreeK

end
