module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11CheckInputs

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m11O4Check : Bool :=
  m11Invs.all fun y => !(y * m11gA == m11gA * y) || y == m11gA ||
    m11Elements.any fun g => g * m11gA == m11gA * g &&
      (orderIs (y * (g * y * g⁻¹)) 4 || orderIs (y * (g * y * g⁻¹)) 8)

end CFSG.Quasithin.B45Exc
