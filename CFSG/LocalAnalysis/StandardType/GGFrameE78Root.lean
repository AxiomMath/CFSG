module

public import Certificates.Certificate709549
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType.FrameRoute

theorem exists_neg_eigen_add_smul_of_feTx {v y : FEVec 7}
    (hv : (feTx 7 v).ncard = 21 ∨ (feTx 7 v).ncard = 36)
    (hy : 13 ≤ (feTx 7 v ∩ feTx 7 y).ncard) :
    ∃ c : ZMod 3, ∃ t ∈ feT 7, t.mulVec (y + c • v) = -(y + c • v) :=
  Certificates.certificate709549 hv hy

end CFSG.StandardType.FrameRoute

end
