
module

public import Certificates.Certificate9206Base
import all Certificates.Certificate9206Base

public import Certificates.Data.CFSGNative.Bridge.Fi23GPL
import Certificates.Kernel.Sporadic.Fi23Br.Rels
public import CFSG.Sporadic.Fi23.SetupBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Bridge.Fi23GPL.Native in
theorem certificate9206 : imgWords.size = 10 ∧ surjWords.size = 2 ∧
    (∀ w ∈ surjWords, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 10) ∧
    ∃ X : ℕ → Matrix (Fin 253) (Fin 253) (ZMod 3),
    (∀ k < 10, X k = (imgWords[k]!.map fun z =>
      if z = 1 then mA else if z = -1 then mA⁻¹ else if z = 2 then mB else mB⁻¹).prod) ∧
    (∀ v ∈ rels, (v.map fun l => if l.2 then X l.1 else (X l.1)⁻¹).prod = 1) ∧
    (surjWords[0]!.map fun z => if 0 < z then X (z - 1).toNat else (X (-z - 1).toNat)⁻¹).prod =
      mA ∧
    (surjWords[1]!.map fun z => if 0 < z then X (z - 1).toNat else (X (-z - 1).toNat)⁻¹).prod =
      mB :=
  KernelSpor.Fi23Rels.facts

end Certificates
