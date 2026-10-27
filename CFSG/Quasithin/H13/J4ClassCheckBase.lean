
module

public import Certificates.Data.CFSGNative.H13.J4Class
public meta import Certificates.Data.CFSGNative.H13.J4Class
public import Certificates.Data.CFSGNative.H13.J4Elems
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Sporadic.Schreier.J4SNative
public meta import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SKCentBase
public meta import CFSG.Sporadic.Schreier.J4SKCentBase
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Quasithin.H13.J4ClassCheckInputs

@[expose] public section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4Schreier (Pair mulP invP powP oneP wordP An Bn Xn Yn Zn etaP O xColumns
  yColumns xInvColumns yInvColumns powCols wordCols app11)
open CFSG.Quasithin.H13.J4.Native (imCols colsBounded)

end CFSG.Quasithin.H13.J4
