
module


public import CFSG.Monster.B.Fischer.InducedChecksInputs
import Certificates.Kernel.MonsterB.Ind3034.Final

public section

open CFSG.Monster.B.Fischer

namespace Certificates

open CFSG.Monster.B.Fischer in
theorem certificate3034 : (∀ g < 2, ∀ t < 22, (indM22Gen g)[t]! = genAB' g t)
    ∧ (∀ g < 2, ∀ u < 1024, (indM22Gen g)[22 + u]! = 22 + linW g u)
    ∧ ((List.range 2).all (fun g => (List.range 77).all (zCheckOne g)) = true)
    ∧ (∀ p < 5760, ∀ q < 32, (dCert.pts[p]!)[22 + q]! < 32)
    ∧ (∀ t < 10, (∀ n < 22, (indTransGen t)[n]! = n) ∧
       (∀ u < 1024, (indTransGen t)[22 + u]! = 22 + (u ^^^ 2 ^ t)) ∧
       ∀ i < 77, zShift t i < 32 ∧ ∀ q < 32,
         (indTransGen t)[1046 + 32 * i + q]! = 1046 + 32 * i + (q ^^^ zShift t i))
    ∧ (∀ t < 10, ∀ i < 77,
       red 17 pivQ rowQ (wordMask (invWord (blockWord i)) (spreadW (2 ^ t)) ^^^
         spreadQ (zShift t i)) = 0)
    ∧ (∀ g < 2, (indM22Gen g).size = 3510) :=
  ⟨CFSG.KC.Ind3034.check_X, CFSG.KC.Ind3034.check_W, CFSG.KC.Ind3034.check_Z,
    CFSG.KC.Ind3034.check_D, CFSG.KC.Ind3034.check_T, CFSG.KC.Ind3034.check_S,
    CFSG.KC.Ind3034.check_size⟩

end Certificates
