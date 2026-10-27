
module


public import Certificates.Certificate6055

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount
open CFSG.Sporadic.Bridge.Fi23GPL.Native (rels)

theorem fiRelFixes_ok_AD :
    wordLin (fiRelW rels[55]!) = 1 ∧ wordLin (fiRelW rels[56]!) = 1 :=
  Certificates.certificate6055

end CFSG.Monster.Existence
