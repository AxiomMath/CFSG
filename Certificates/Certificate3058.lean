
module

public import Certificates.Certificate3058Base

public import CFSG.Monster.B.TwoA.Sp8.A8Inputs

public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.KC.KDense CFSG.KC.Trace6091

namespace CertificateChecks.Batch3058

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.KC.KDense CFSG.KC.Trace6091

end CertificateChecks.Batch3058

namespace Certificates

open CertificateChecks.Batch3058 in
open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B in
theorem certificate3058 : ySqRowCheck Model.eYN = true := by
  unfold ySqRowCheck
  refine List.all_eq_true.2 fun c hc => ?_
  have hp : Model.pi0N c < 4096 := by
    unfold Model.pi0N
    have hc' : c < 2 ^ 12 := List.mem_range.1 hc
    split
    · exact Nat.xor_lt_two_pow hc' (by norm_num)
    · simpa using hc'
  have h0 := pi0_bit c
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  constructor
  · simp only [Model.eYN, Bool.false_eq_true, ite_false]
    rw [shift_eq h0, pi0_of (bit_60 h0), shift_back h0, ← theta_eq hp h0]
    simp
  · simp only [Model.eYN, ite_true]
    rw [pi0_of h0]
    simp

end Certificates
