
module


public import CFSG.Monster.B.Fischer.Fi22FaithfulCheckInputs
import Certificates.Kernel.Sporadic.Fi22.C3152

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer.Native CFSG.Monster.B.Fischer CFSG.F3.Native in
theorem certificate3152 : distinctOK fi22FormsBytes 4 = true ∧
      actionOK fi22FormsBytes (fi22ChainGen 0) CFSG.Sporadic.Fi22.Native.matA 4 = true ∧
      actionOK fi22FormsBytes (fi22ChainGen 1) CFSG.Sporadic.Fi22.Native.matB 4 = true ∧
      pullbackOK fi22InvFormBytes 0 fi22InvFormBytes 0 CFSG.Sporadic.Fi22.Native.matA
        (CFSG.F3.Native.transpose 77 CFSG.Sporadic.Fi22.Native.matA) = true ∧
      pullbackOK fi22InvFormBytes 0 fi22InvFormBytes 0 CFSG.Sporadic.Fi22.Native.matB
        (CFSG.F3.Native.transpose 77 CFSG.Sporadic.Fi22.Native.matB) = true ∧
      CFSG.F3.Native.wfM fi22Bi = true ∧ fi22Bi.size = 77 ∧
      eqM 77 (CFSG.F3.Native.mul 77 (polarRows fi22InvFormBytes 0) fi22Bi) (CFSG.F3.Native.idM 77) = true ∧
      sepOK 77 fi22SepMats fi22SepTerms fi22SepVec fi22SepK fi22SepP fi22SepTinv
        fi22SepTree = true := KernelSpor.F3152.facts3152

end Certificates
