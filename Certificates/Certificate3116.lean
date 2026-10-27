
module


public import CFSG.Sporadic.Co2Cert.FaithfulCheckInputs
import Certificates.Kernel.Sporadic.Co2.FaithfulK

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native in
theorem certificate3116 : co2PackedVecs.size = 2300 ∧
      (∀ i < 2300, co2PackedVecs[i]! < 2 ^ 22 ∧ co2PackedVecs[i]! ≠ 0 ∧
        ∀ j < 2300, co2PackedVecs[i]! = co2PackedVecs[j]! → i = j) ∧
      co2BasisRows.size = 22 ∧ mulRows 22 co2BasisInv co2BasisRows = idRows 22 ∧
      (∀ i < 2300, CFSG.Sporadic.SmallF2.Native.vecMulN 22 (transposeRows 22 co2RowsA) co2PackedVecs[i]! =
        co2PackedVecs[(co2OrigArrs[0]!)[i]!]!) ∧
      (∀ i < 2300, CFSG.Sporadic.SmallF2.Native.vecMulN 22 (transposeRows 22 co2RowsB) co2PackedVecs[i]! =
        co2PackedVecs[(co2OrigArrs[1]!)[i]!]!) ∧
      mulRows 22 co2RowsA co2RowsA = idRows 22 ∧ CFSG.Sporadic.SmallF2.Native.powRows 22 co2RowsB 5 = idRows 22 := KernelSpor.Co2Faith.facts

end Certificates
