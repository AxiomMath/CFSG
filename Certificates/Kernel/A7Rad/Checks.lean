module

public import Certificates.Kernel.A7Rad.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelA7Rad

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.A7Rad CFSG.KD.A7Rad

theorem ch134003_closed_D8 : closedB D8 8 = true := by quickRfl
theorem ch134003_closed_V4 : closedB V4 4 = true := by quickRfl
theorem ch134003_closed_Tf : closedB Tf 4 = true := by quickRfl
theorem ch134003_closed_Tg : closedB Tg 4 = true := by quickRfl
theorem ch134003_closed_A5a : closedB LA 60 = true := by quickRfl
theorem ch134003_closed_A5b : closedB LB 60 = true := by quickRfl

theorem ch134003_valid_D8 : validB D8 8 = true := by quickRfl
theorem ch134003_valid_V4 : validB V4 4 = true := by quickRfl
theorem ch134003_valid_V4' : validB V4' 4 = true := by quickRfl
theorem ch134003_valid_C4 : validB C4 4 = true := by quickRfl
theorem ch134003_valid_Z1 : validB Z1 2 = true := by quickRfl
theorem ch134003_valid_Z2 : validB Z2 2 = true := by quickRfl
theorem ch134003_valid_Z3 : validB Z3 2 = true := by quickRfl
theorem ch134003_valid_Z4 : validB Z4 2 = true := by quickRfl
theorem ch134003_valid_Z5 : validB Z5 2 = true := by quickRfl
theorem ch134003_valid_Tf : validB Tf 4 = true := by quickRfl
theorem ch134003_valid_Tg : validB Tg 4 = true := by quickRfl
theorem ch134003_valid_A5a : validB LA 60 = true := by quickRfl
theorem ch134003_valid_A5b : validB LB 60 = true := by quickRfl

theorem ch134003_pow4_D8 : pow4B D8 8 = true := by quickRfl
theorem ch134003_pow4_V4 : pow4B V4 4 = true := by quickRfl
theorem ch134003_pow4_Tf : pow4B Tf 4 = true := by quickRfl
theorem ch134003_pow4_Tg : pow4B Tg 4 = true := by quickRfl

theorem ch134003_nonab_D8 : nonabB D8 8 = true := by quickRfl
theorem ch134003_one_E1 : Nat.beq (fld E1 0) (one 7) = true := by quickRfl
theorem ch134003_sub_V4 : subB V4 4 LA 60 = true := by quickRfl
theorem ch134003_sub_V4' : subB V4' 4 LB 60 = true := by quickRfl
theorem ch134003_nonab_A5a : nonabB LA 60 = true := by quickRfl
theorem ch134003_nonab_A5b : nonabB LB 60 = true := by quickRfl

theorem ch134003_three_A5a : threeB LA 60 WA = true := by quickRfl
theorem ch134003_three_A5b : threeB LB 60 WB = true := by quickRfl

theorem ch134003_lat : latB D8 8 tenM = true := by quickRfl
theorem ch134003_le_E1 : subB E1 1 D8 8 = true := by quickRfl
theorem ch134003_le_Z1 : subB Z1 2 D8 8 = true := by quickRfl
theorem ch134003_le_Z2 : subB Z2 2 D8 8 = true := by quickRfl
theorem ch134003_le_Z3 : subB Z3 2 D8 8 = true := by quickRfl
theorem ch134003_le_Z4 : subB Z4 2 D8 8 = true := by quickRfl
theorem ch134003_le_Z5 : subB Z5 2 D8 8 = true := by quickRfl
theorem ch134003_le_C4 : subB C4 4 D8 8 = true := by quickRfl
theorem ch134003_le_V4 : subB V4 4 D8 8 = true := by quickRfl
theorem ch134003_le_V4' : subB V4' 4 D8 8 = true := by quickRfl
theorem ch134003_le_D8 : subB D8 8 D8 8 = true := by quickRfl

theorem ch134003_norm_Z1 : normB Z1 2 V4 4 (pow 7 R 2) = true := by quickRfl
theorem ch134003_norm_Z2 : normB Z2 2 Tf 4 F = true := by quickRfl
theorem ch134003_norm_Z3 : normB Z3 2 Tg 4 (mul 7 (pow 7 R 2) F) = true := by quickRfl
theorem ch134003_norm_Z4 : normB Z4 2 V4 4 (mul 7 R F) = true := by quickRfl
theorem ch134003_norm_Z5 : normB Z5 2 V4 4 (mul 7 (pow 7 R 3) F) = true := by quickRfl
theorem ch134003_norm_C4 : normB C4 4 D8 8 (pow 7 R 2) = true := by quickRfl

theorem ch134003_conj_Z1 : conjB V4 4 Z1 2 = true := by quickRfl
theorem ch134003_conj_Z2 : conjB Tf 4 Z2 2 = true := by quickRfl
theorem ch134003_conj_Z3 : conjB Tg 4 Z3 2 = true := by quickRfl
theorem ch134003_conj_Z4 : conjB V4 4 Z4 2 = true := by quickRfl
theorem ch134003_conj_Z5 : conjB V4 4 Z5 2 = true := by quickRfl
theorem ch134003_conj_C4 : conjB D8 8 C4 4 = true := by quickRfl

theorem ch134003_ex_Z1 : exB V4 4 Z1 2 = true := by quickRfl
theorem ch134003_ex_Z2 : exB Tf 4 Z2 2 = true := by quickRfl
theorem ch134003_ex_Z3 : exB Tg 4 Z3 2 = true := by quickRfl
theorem ch134003_ex_Z4 : exB V4 4 Z4 2 = true := by quickRfl
theorem ch134003_ex_Z5 : exB V4 4 Z5 2 = true := by quickRfl
theorem ch134003_ex_C4 : exB D8 8 C4 4 = true := by quickRfl

end CertificateChecks.KernelA7Rad

end
