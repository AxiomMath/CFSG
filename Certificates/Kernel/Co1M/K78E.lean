module

public import Certificates.Kernel.Co1M.D10078
public import Certificates.Data.Kernel.Co1M.U6Odd
public import Certificates.Data.Kernel.Co1FixList
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.InvFam CFSG.KC.SortTree CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT
  CFSG.KC.U6Odd CFSG.KC.Co1Fix

theorem k78_tr : allN (lenL R78) (fun i => Nat.beq (trK 24 (getL 0 R78 i)) (getL 0 RT78 i)) = true := by
  quickRfl

theorem k78_g11 : andB (Nat.beq (powK 24 (getL 0 R78 22) 11) (idF 24))
    (andB (notB (Nat.beq (getL 0 R78 22) (idF 24)))
      (fixAllK RT78 [22] [2, 16584974, 13392743, 15259617])) = true := by quickRfl

theorem k78_g7 : andB (Nat.beq (powK 24 (getL 0 R78 38) 7) (idF 24))
    (andB (notB (Nat.beq (getL 0 R78 38) (idF 24)))
      (fixAllK RT78 [38] [2, 16584974, 12539971, 10361096, 459969])) = true := by quickRfl

theorem k78_g5 : andB (Nat.beq (powK 24 (getL 0 R78 54) 5) (idF 24))
    (andB (notB (Nat.beq (getL 0 R78 54) (idF 24)))
      (fixAllK RT78 [54] [2, 16584974, 1095512, 9326441, 5595851])) = true := by quickRfl

theorem k78_lv11 : andB (fixAllK RT78 [7, 8, 9, 10, 11] [2, 16584974])
    (fixAllK RT78 [12, 13, 14, 15, 16] [2, 16584974, 13392743]) = true := by quickRfl

theorem k78_lv7 : andB (fixAllK RT78 [7, 8, 9, 10, 11] [2, 16584974])
    (andB (fixAllK RT78 [23, 24, 25, 26, 27] [2, 16584974, 12539971])
      (fixAllK RT78 [28, 29, 30, 31, 32] [2, 16584974, 12539971, 10361096])) = true := by quickRfl

theorem k78_lv5 : andB (fixAllK RT78 [7, 8, 9, 10, 11] [2, 16584974])
    (andB (fixAllK RT78 [39, 40, 41, 42, 43] [2, 16584974, 1095512])
      (fixAllK RT78 [44, 45, 46, 47, 48] [2, 16584974, 1095512, 9326441])) = true := by quickRfl

theorem k78_fix11 : andB (fixK 24 (getL 0 RT78 22) 0 F1178 Y1178 (lenL F1178) (pw2 (lenL F1178)) 0)
    (fixListK (getL 0 RT78 22) (getL 0 RT78 22) F1178 W1178) = true := by quickRfl

theorem k78_fix7 : andB (fixK 24 (getL 0 RT78 38) 0 F778 Y778 (lenL F778) (pw2 (lenL F778)) 0)
    (fixListK (getL 0 RT78 38) (getL 0 RT78 38) F778 W778) = true := by quickRfl

theorem k78_fix5 : andB (fixK 24 (getL 0 RT78 54) 0 F578 Y578 (lenL F578) (pw2 (lenL F578)) 0)
    (fixListK (getL 0 RT78 54) (getL 0 RT78 54) F578 W578) = true := by quickRfl

theorem k78_cl : andB (fixAllK RT78 [17, 18] [2, 16584974, 13392743, 15259617])
    (andB (allN 2 fun l => Nat.beq (mulF 24 (getL 0 R78 (getL 0 [17, 18] l)) (getL 0 X78 l)) (idF 24))
      (Nat.beq (canonK (getL 0 R78 22)) (getL 0 R78 22))) = true := by quickRfl

theorem k78_clT : chunksK (actH [getL 0 R78 17, getL 0 R78 18] X78) 2 (getL 0 R78 22)
    (recT cl11L78 5 587) 60 576 4 6 32 0 2 = true := by quickRfl

theorem k78_n : andB (fixAllK RT78 [55, 56] [2, 16584974])
    (allL [55, 56] fun x => normK (getL 0 R78 x) (getL 0 R78 54) 5) = true := by quickRfl

theorem k78_nT : chunksK (actR [getL 0 R78 55, getL 0 R78 56]) 2 (idF 24) (recT n5L78 5 588) 120 576
    4 7 32 0 4 = true := by quickRfl

theorem k78_s : andB (fixAllK RT78 [64, 65, 66] [2, 16584974])
    (allN 3 fun l => Nat.beq (powK 24 (getL 0 R78 (getL 0 [64, 65, 66] l)) (getL 0 [9, 3, 3] l))
      (idF 24)) = true := by quickRfl

theorem k78_sT : chunksK (actR [getL 0 R78 64, getL 0 R78 65, getL 0 R78 66]) 3 (idF 24)
    (recT s0L78 5 592) 729 576 4 10 32 0 23 = true := by quickRfl

theorem k78_sC : closeOK (actR [getL 0 R78 64, getL 0 R78 65, getL 0 R78 66]) 3 (recT s0L78 5 592)
    (fun i k => fget (recT e0L78 6 30 i) k 10) 729 576 32 23 = true := by quickRfl

theorem k78_sW : allN 729 (fun i => witK (fun j => valF 576 (recT s0L78 5 592 j)) 729 i
    (recT c0L78 5 60 i)) = true := by quickRfl

theorem k78_sB : Nat.ble (zerosK 729 (recT c0L78 5 60)) 27 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
