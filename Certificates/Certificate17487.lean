module

public import CFSG.YGroups.Y443.Native.EdgeNoncommInputs
public import Certificates.Data.TabMSevenQ
import Certificates.Kernel.KDenseP.Q7

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.HardMathSupport.Dickson.I271.TabMSeven in
theorem certificate17487 :
    qAt (aV ()) = true ∧ qAt (CFSG.YGroups.Y443Native.bV ()) = true ∧ qAt (wV ()) = true ∧
      EdgeNoncomm.moveCheck qZ (aV ()) = true ∧ EdgeNoncomm.moveCheck CFSG.HardMathSupport.Dickson.I271.TabMSeven.qF (aV ()) = true ∧
      EdgeNoncomm.moveCheck qT (wV ()) = true := KernelKDenseP.Q7.c17487

end Certificates
