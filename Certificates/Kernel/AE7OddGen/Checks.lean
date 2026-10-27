module

public import Certificates.Data.AE7OddGen

public section

namespace CFSG.KD.AE7OddGen

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117
  Certificates.AE7OddGen

theorem ae7g_comm : commOK (Lrel id) (ofVec (indL [4, 5])) (ofVec (indL [0, 1, 2, 3])) = true := by
  decide +kernel

theorem ae7g_ae : aeOK (Lrel id) = true := by decide +kernel

theorem ae7g_pairs : pairsOK (Lrel id) = true := by decide +kernel

theorem ae7g_cycles : cyclesOK (Lrel id) = true := by decide +kernel

end CFSG.KD.AE7OddGen

end
