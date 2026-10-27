module

public import Certificates.Data.Kernel.B45M12.Four
public import Certificates.Data.SmithB45MatM12Nor
public import Certificates.Kernel.C260404.Pins

public section

namespace CFSG.KD.C260404

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12

@[expose] noncomputable def B16c : List (ℕ × ℕ) := colsF4 16 B16Rows

@[expose] noncomputable def P16c : List (ℕ × ℕ) := colsF4 32 P16Rows

@[expose] noncomputable def g16 (T : List ℕ) : List (ℕ × ℕ) := mulF4 P16c (mulF4 (ofF2 T) B16c)

theorem f4 : subF4 32 16 B16c P16c [ofF2 T32A, ofF2 T32B] = true ∧
    norF4 16 c16aTermWords c16aTermCoeffs c16aQRows c16aQiRows c16aRRows c16aSiRows c16aTiRows
      c16aW c16aSpin c16aDual (g16 T32A) (g16 T32B) = true ∧
    norF4 16 c16bTermWords c16bTermCoeffs c16bQRows c16bQiRows c16bRRows c16bSiRows c16bTiRows
      c16bW c16bSpin c16bDual (frobF4 (g16 T32A)) (frobF4 (g16 T32B)) = true ∧
    traceK 16 (mulF4 (g16 T32A) (g16 T32B)) 2 = true ∧
    traceK 16 (mulF4 (frobF4 (g16 T32A)) (frobF4 (g16 T32B))) 3 = true := by
  decide +kernel

end CFSG.KD.C260404

end
