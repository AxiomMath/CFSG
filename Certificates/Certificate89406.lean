module

public import CFSG.Quasithin.H13.AS91Sec4SixInputs
import Certificates.Kernel.AS91K468.Checks46
import Certificates.Kernel.AS91K468.Checks46B
import CFSG.Certificates.Kernel.AS91K468.Sound46C

public section

namespace Certificates

open Certificates.Kernel.AS91K468 CertificateChecks.KernelAS91K468 CFSG.KD.AS91K46 CFSG.KD.AS91K46C

open CFSG.Quasithin.H13.AS91 in
theorem certificate89406 : Two.ok46 () = true :=
  ok46_ofW ch89406_words ch89406_w1 ch89406_eb ch89406_trans ch89406_pnodup pfL ch89406_pf
    (fk 0) (fk 1) (fk 2) (fk 3) (fk 4) ch89406_f0
    (round_walkNE pfL 20 1 (fk 0) (fk 0) (fk 1) (ck 0) (dk 0) ch89406_e0
      (lt_snoc lt_zero' ch89406_q0_0))
    (round_walkNE pfL 20 6 (fk 1) (fk 1 ++ fk 0) (fk 2) (ck 1) (dk 1) ch89406_e1
      (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc lt_zero'
        ch89406_q1_0) ch89406_q1_1) ch89406_q1_2) ch89406_q1_3) ch89406_q1_4) ch89406_q1_5))
    (round_walkNE pfL 20 19 (fk 2) (fk 2 ++ (fk 1 ++ fk 0)) (fk 3) (ck 2) (dk 2) ch89406_e2
      (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc
        (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc
        (lt_snoc lt_zero'
        ch89406_q2_0) ch89406_q2_1) ch89406_q2_2) ch89406_q2_3) ch89406_q2_4) ch89406_q2_5)
        ch89406_q2_6) ch89406_q2_7) ch89406_q2_8) ch89406_q2_9) ch89406_q2_10) ch89406_q2_11)
        ch89406_q2_12) ch89406_q2_13) ch89406_q2_14) ch89406_q2_15) ch89406_q2_16)
        ch89406_q2_17) ch89406_q2_18))
    (round_walkNE pfL 20 8 (fk 3) (fk 3 ++ (fk 2 ++ (fk 1 ++ fk 0))) (fk 4) (ck 3) (dk 3)
      ch89406_e3
      (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc lt_zero'
        ch89406_q3_0) ch89406_q3_1) ch89406_q3_2) ch89406_q3_3) ch89406_q3_4) ch89406_q3_5)
        ch89406_q3_6) ch89406_q3_7))
    (round_walk pfL 20 1 (fk 4) (fk 4 ++ (fk 3 ++ (fk 2 ++ (fk 1 ++ fk 0)))) [] (ck 4) (dk 4)
      ch89406_e4 (lt_snoc lt_zero' ch89406_q4_0))
    (jAll2_chunks pfL 20 1 (fk 0) (chunksEnd_len' ch89406_e0) (lt_snoc lt_zero' ch89406_b0_0))
    (jAll2_chunks pfL 20 6 (fk 1) (chunksEnd_len' ch89406_e1)
      (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc lt_zero'
        ch89406_b1_0) ch89406_b1_1) ch89406_b1_2) ch89406_b1_3) ch89406_b1_4) ch89406_b1_5))
    (jAll2_chunks pfL 20 19 (fk 2) (chunksEnd_len' ch89406_e2)
      (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc
        (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc
        (lt_snoc lt_zero'
        ch89406_b2_0) ch89406_b2_1) ch89406_b2_2) ch89406_b2_3) ch89406_b2_4) ch89406_b2_5)
        ch89406_b2_6) ch89406_b2_7) ch89406_b2_8) ch89406_b2_9) ch89406_b2_10) ch89406_b2_11)
        ch89406_b2_12) ch89406_b2_13) ch89406_b2_14) ch89406_b2_15) ch89406_b2_16)
        ch89406_b2_17) ch89406_b2_18))
    (jAll2_chunks pfL 20 8 (fk 3) (chunksEnd_len' ch89406_e3)
      (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc (lt_snoc lt_zero'
        ch89406_b3_0) ch89406_b3_1) ch89406_b3_2) ch89406_b3_3) ch89406_b3_4) ch89406_b3_5)
        ch89406_b3_6) ch89406_b3_7))
    (jAll2_chunks pfL 20 1 (fk 4) (chunksEnd_len ch89406_e4) (lt_snoc lt_zero' ch89406_b4_0))

end Certificates
