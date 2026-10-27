module

public import CFSG.Sporadic.Schreier.J1CountCheckInputs
public meta import CFSG.Sporadic.Schreier.J1Tables
public meta import CFSG.Sporadic.Schreier.ClassSum
import Certificates.Kernel.SporSch.J1.Count2166

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native in
theorem certificate2166 : (invOK 3080 j1ATbl j1AInvTbl = true ∧ invOK 3080 j1BTbl j1BInvTbl = true ∧
      ordTest 3080 2 j1ATbl = true ∧ ordTest 3080 3 j1BTbl = true ∧
      pairTest 3080 7 19 2 3 j1ATbl j1BTbl = true
    )
    ∧ ((j1OrderTables 2).length = 1463)
    ∧ ((j1OrderTables 3).length = 5852)
    ∧ (classOK 3080 j1GenTbls j1GenInvTbls (j1OrderTables 2) 2000 = true)
    ∧ (classTotal 3080 j1GenTbls j1GenInvTbls (j1OrderTables 2) (j1OrderTables 3) 2000 7 19 2 3 =
      175560
    ) := KernelSporSch.J1.countFacts

end Certificates
