module

public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Gen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import Certificates.Kernel.Sp43K.GlueSyl

public section

namespace Certificates

theorem certificate1322001 : Nat.card (Matrix.symplecticGroup (Fin 2) (ZMod 3)) = 51840 ∧
    ∀ W : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3)),
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.oPPrimeHull 3 W = W → CFSG.Sp43.GenProp W := CFSG.KD.Sp43K.sp43_facts

end Certificates
