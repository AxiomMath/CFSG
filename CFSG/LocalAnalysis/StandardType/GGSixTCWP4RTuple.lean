module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Inv

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Tuples

variable {τ : Tag} {S : TcrSys}

theorem tcr_getD_ofFn_nat {n : ℕ} (f : Fin n → ℕ) (j : Fin n) :
    (List.ofFn f).getD j.val 0 = f j := by
  simp [List.getD_eq_getElem?_getD]

end Tuples

end CFSG.StandardType.TableCRes

end
