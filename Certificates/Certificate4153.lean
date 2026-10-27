module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore
import Certificates.Kernel.LocalQT.Small.C4153

public section

namespace Certificates

open CFSG.KD.LQT.C4153 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts in
theorem certificate4153 : (Core.pslLit.all (fun x => x == Core.cid || Core.cpow x 45 != Core.cid ||
          Core.pslLit.all fun u => Core.cmul u x != Core.cmul x u || Core.cpow u 45 == Core.cid) =
            true) := CFSG.KC.LQT.S.s4153 _ hc hv hk

end Certificates
