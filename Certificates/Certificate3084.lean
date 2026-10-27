
module

public import Certificates.Certificate3084Base
import Certificates.Kernel.J4Count.PrimBase
import CFSG.Sporadic.Schreier.J4SOrbitsBase
meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.J4.QT2LocPath
public import CFSG.Sporadic.J4.Action

public import CFSG.Sporadic.J4.Local
import Certificates.Kernel.J4Count.Prim
import CFSG.Sporadic.Schreier.J4SNative
import CFSG.Sporadic.Schreier.J4SCols
import CFSG.Sporadic.Schreier.J4SFormData
import CFSG.Sporadic.Schreier.J4SNoCompData
meta import CFSG.Sporadic.Schreier.J4SNoCompData
import CFSG.Sporadic.Schreier.J4SOrbits
meta import CFSG.Sporadic.Schreier.J4SOrbits
import Certificates.Certificate4008
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.J4.CertParts
public import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CertificateChecks

theorem certificate3084 : CFSG.Sporadic.J4.J4Facts :=
    { mat := KernelJ4Q.matFacts
      cardHj := KernelJ4Count.card_Hj'
      cardJ := KernelJ4Hub.card_J'
      stab := fun x hx => by
        rw [← KernelJ4Count.stabilizer_v_eq_Hj', MulAction.mem_stabilizer_iff,
          KernelJ4Count.v_eq_root]
        exact hx
      coatom := KernelJ4Count.Prim.isCoatom_Hj'
      simple := KernelJ4Count.Prim.isSimpleGroup_J'
      cosets := Certificates.certificate4008.1
      sizes := Certificates.certificate4008.2 }

end Certificates
