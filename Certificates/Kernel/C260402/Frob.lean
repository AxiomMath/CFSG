module

public import Certificates.Data.Kernel.B45M22.Defs
public import Certificates.Data.SmithB45MatM22Mod

public section

namespace CFSG.KD.C260402

open CFSG.KC.B45M12 CFSG.KC.B45M22 CFSG.Quasithin.B45Mat.M22

theorem frobB70 :
    eqF4 70 (B70bRows.map (deint 7)) (frobF4 (B70aRows.map (deint 7))) = true := by
  decide +kernel

theorem P70b_rows : P70bRows = P70aRows := by
  decide +kernel

end CFSG.KD.C260402

end
