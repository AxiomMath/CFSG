module

public import Certificates.Certificate8954

public section

namespace CFSG.Monster.Existence.Co2Bridge

open CFSG.Sporadic.SmallF2.Native

theorem transposeRows_rowsA :
    transposeRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsA = atRows :=
  Certificates.certificate8954.1

theorem transposeRows_rowsB :
    transposeRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB = btRows :=
  Certificates.certificate8954.2.1

theorem rowsA_sq : mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsA
    CFSG.Sporadic.Co2.Native.co2Data.rowsA = idRows 22 :=
  Certificates.certificate8954.2.2.1

theorem rowsB_pow_five :
    mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
    (mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
      (mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
        (mulRows 22 CFSG.Sporadic.Co2.Native.co2Data.rowsB
          CFSG.Sporadic.Co2.Native.co2Data.rowsB))) = idRows 22 :=
  Certificates.certificate8954.2.2.2.1

theorem mulRows_e_eInv : mulRows 22 eRows eInvRows = idRows 22 :=
  Certificates.certificate8954.2.2.2.2.1

theorem mulRows_eInv_e : mulRows 22 eInvRows eRows = idRows 22 :=
  Certificates.certificate8954.2.2.2.2.2.1

theorem xWord_lt : ∀ l ∈ xWord, l < 24 :=
  Certificates.certificate8954.2.2.2.2.2.2.1

theorem yWord_lt : ∀ l ∈ yWord, l < 24 :=
  Certificates.certificate8954.2.2.2.2.2.2.2.1

theorem xCheck :
    ∀ i < 22, actWordQ xWord (vecMulN 22 eRows (1 <<< i)) =
    vecMulN 22 eRows (vecMulN 22 atRows (1 <<< i)) :=
  Certificates.certificate8954.2.2.2.2.2.2.2.2.1

theorem yCheck :
    ∀ i < 22, actWordQ yWord (vecMulN 22 eRows (1 <<< i)) =
    vecMulN 22 eRows (vecMulN 22 btRows (1 <<< i)) :=
  Certificates.certificate8954.2.2.2.2.2.2.2.2.2

end CFSG.Monster.Existence.Co2Bridge
