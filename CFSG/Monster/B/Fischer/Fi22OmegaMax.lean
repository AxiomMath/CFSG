module

public import Certificates.Certificate1023301

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.SetOrbit CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open scoped Pointwise

theorem fi22Omega_index_stabilizer :
    (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)).index = 61776 :=
  Certificates.certificate1023301.1

theorem fi22Omega_card_stabilizer :
    Nat.card (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)) = 1045094400 := by
  have h := (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)).card_mul_index
  rw [fi22Omega_index_stabilizer, card_fi22P,
    show (64561751654400 : ℕ) = 1045094400 * 61776 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

theorem i242Y_le_stabilizer_U0 :
    i242Y ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (ptSet 3510 fi22OmegaU0) :=
  Certificates.certificate1023301.2.2.1

theorem fi22FiveQ_le_stabilizer_U0 :
    fi22FiveQ ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (ptSet 3510 fi22OmegaU0) :=
  Certificates.certificate1023301.2.2.2

theorem i242Y_le_fi22P :
    i242Y ≤ fi22P :=
  i242Y_le_J.trans (iSup_le fun i => fi22FiveD_le_P i)

theorem fi22Omega_isCoatom :
    IsCoatom (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)) :=
  Certificates.certificate1023301.2.1

end CFSG.Monster.B.Fischer
