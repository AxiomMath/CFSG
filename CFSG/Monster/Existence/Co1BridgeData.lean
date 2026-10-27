module

public import Certificates.Certificate8955

public section

namespace CFSG.Monster.Existence.Co1Bridge

open CFSG.Monster.VisCert CFSG.Sporadic.SmallF2.Native

theorem transposeRows_rowsA :
    transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsA = atRows :=
  Certificates.certificate8955.1

theorem transposeRows_rowsB :
    transposeRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB = btRows :=
  Certificates.certificate8955.2.1

theorem rowsA_sq : mulRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsA
    CFSG.Sporadic.Co1.Native.co1Data.rowsA = idRows 24 :=
  Certificates.certificate8955.2.2.1

theorem rowsB_cube :
    mulRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB
    (mulRows 24 CFSG.Sporadic.Co1.Native.co1Data.rowsB CFSG.Sporadic.Co1.Native.co1Data.rowsB) =
      idRows 24 :=
  Certificates.certificate8955.2.2.2.1

theorem mulRows_e_eInv : mulRows 24 eRows eInvRows = idRows 24 :=
  Certificates.certificate8955.2.2.2.2.1

theorem mulRows_eInv_e : mulRows 24 eInvRows eRows = idRows 24 :=
  Certificates.certificate8955.2.2.2.2.2.1

theorem xWord_lt : ∀ g ∈ xWord, g < 15 :=
  Certificates.certificate8955.2.2.2.2.2.2.1

theorem yWord_lt : ∀ g ∈ yWord, g < 15 :=
  Certificates.certificate8955.2.2.2.2.2.2.2.1

theorem xCheck :
    ∀ i < 24, actWord frameMatrices xWord (vecMulN 24 eRows (1 <<< i)) =
    vecMulN 24 eRows (vecMulN 24 atRows (1 <<< i)) :=
  Certificates.certificate8955.2.2.2.2.2.2.2.2.1

theorem yCheck :
    ∀ i < 24, actWord frameMatrices yWord (vecMulN 24 eRows (1 <<< i)) =
    vecMulN 24 eRows (vecMulN 24 btRows (1 <<< i)) :=
  Certificates.certificate8955.2.2.2.2.2.2.2.2.2

end CFSG.Monster.Existence.Co1Bridge
