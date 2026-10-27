module

public import Certificates.Data.Kernel.Stroth77.SplitK

public section

namespace CFSG.KC.Stroth77SP

@[expose] def w4OK (D : Tabs) : Bool :=
  l256.all fun c => !memB D.W4M c || l16.any fun r => phiS D r == c

end CFSG.KC.Stroth77SP
