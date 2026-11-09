module

public import Certificates.Data.Kernel.B45Ind.M24
public import Certificates.Data.Kernel.B45Ind.FlagK

public section

namespace CFSG.KD.C260432

open CFSG.KC.B45Ind CFSG.Quasithin.B45Mat.Ind

theorem flag2_b :
    (baseOKK (24 * m24Xd 2) (m24P 2) (invColsK (24 * m24Xd 2) (m24P 2)) &&
      nsOK (24 * m24Xd 2) (m24Ns 2)) = true := by
  decide +kernel

theorem flag2_f : flagSide (m24Ns 2) (fun j => m24Std ((m24Typs 2).getD j 0) false)
    (conjColsK (24 * m24Xd 2) (invColsK (24 * m24Xd 2) (m24P 2)) (k24L 2 false) (m24P 2)) =
      true := by
  decide +kernel

theorem flag2_t : flagSide (m24Ns 2) (fun j => m24Std ((m24Typs 2).getD j 0) true)
    (conjColsK (24 * m24Xd 2) (invColsK (24 * m24Xd 2) (m24P 2)) (k24L 2 true) (m24P 2)) =
      true := by
  decide +kernel

theorem flag2 : flag24L 2 = true := by
  rw [flag24L_eq_K]
  exact flagCoreK_of flag2_b flag2_f flag2_t

end CFSG.KD.C260432
