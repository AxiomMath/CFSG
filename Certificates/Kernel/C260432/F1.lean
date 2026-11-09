module

public import Certificates.Data.Kernel.B45Ind.M24
public import Certificates.Data.Kernel.B45Ind.FlagK

public section

namespace CFSG.KD.C260432

open CFSG.KC.B45Ind CFSG.Quasithin.B45Mat.Ind

theorem flag1_b :
    (baseOKK (24 * m24Xd 1) (m24P 1) (invColsK (24 * m24Xd 1) (m24P 1)) &&
      nsOK (24 * m24Xd 1) (m24Ns 1)) = true := by
  decide +kernel

theorem flag1_f : flagSide (m24Ns 1) (fun j => m24Std ((m24Typs 1).getD j 0) false)
    (conjColsK (24 * m24Xd 1) (invColsK (24 * m24Xd 1) (m24P 1)) (k24L 1 false) (m24P 1)) =
      true := by
  decide +kernel

theorem flag1_t : flagSide (m24Ns 1) (fun j => m24Std ((m24Typs 1).getD j 0) true)
    (conjColsK (24 * m24Xd 1) (invColsK (24 * m24Xd 1) (m24P 1)) (k24L 1 true) (m24P 1)) =
      true := by
  decide +kernel

theorem flag1 : flag24L 1 = true := by
  rw [flag24L_eq_K]
  exact flagCoreK_of flag1_b flag1_f flag1_t

end CFSG.KD.C260432
