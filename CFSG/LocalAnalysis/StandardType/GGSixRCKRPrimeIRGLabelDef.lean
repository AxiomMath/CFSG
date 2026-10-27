module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

@[expose] def irgLabel (t : StatedLieTag) (n g : ℕ) : LargeEvenLabel :=
  match t with
  | .PSL => ⟨.A, n - 1, g⟩
  | .PSU => ⟨.twA, n - 1, g⟩
  | .PSp => ⟨.C, n, g⟩
  | .POmegaPlus => ⟨.D, n, g⟩
  | .POmegaMinus => ⟨.twD, n, g⟩
  | .F4 => ⟨.F4, 0, g⟩
  | .E6 => ⟨.E6, 0, g⟩
  | .E7 => ⟨.E7, 0, g⟩
  | .E8 => ⟨.E8, 0, g⟩
  | .twistedE6 => ⟨.twE6, 0, g⟩
  | _ => ⟨.A, 0, 0⟩

end CFSG.StandardType.RCKRP
