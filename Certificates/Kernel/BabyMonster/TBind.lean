module

import CFSG.Certificates.Kernel.BabyMonster.Load
public import CFSG.Certificates.Kernel.BabyMonster.B64Sound
public import CFSG.Certificates.Kernel.BabyMonster.TBind24.All
public import Certificates.Data.Kernel.BabyMonster.TText24
public import Certificates.Kernel.BabyMonster.ForallLt
public import Certificates.Kernel.BabyMonster.Chain
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check24
public import CFSG.Certificates.Kernel.BabyMonster.TBind24.Check0
public import CFSG.Certificates.Kernel.BabyMonster.TBind24.Check1
public import CFSG.Certificates.Kernel.BabyMonster.TBind24.Check2
public import CFSG.Certificates.Kernel.BabyMonster.TBind24.Check3

public section

set_option maxRecDepth 100000

#bm_bool CFSG.KD.TBind24 asc0 (CFSG.KC.BM.B64.asciiOK CFSG.KD.TBind24.C0.CH)
#bm_bool CFSG.KD.TBind24 asc1 (CFSG.KC.BM.B64.asciiOK CFSG.KD.TBind24.C1.CH)
#bm_bool CFSG.KD.TBind24 asc2 (CFSG.KC.BM.B64.asciiOK CFSG.KD.TBind24.C2.CH)
#bm_bool CFSG.KD.TBind24 asc3 (CFSG.KC.BM.B64.asciiOK CFSG.KD.TBind24.C3.CH)

namespace CertificateChecks.KernelBM

open CFSG.KC.YModel CFSG.KC.BM.B64

theorem decChunkC_append (len : Nat) : ∀ (N : Nat) (t u : List Char),
    decChunkC len N (t ++ u) = decChunkC len N t ++ u := by
  induction len with
  | zero => intro N t u; rfl
  | succ len ih =>
    intro N t u
    change List.cons _ (decChunkC len _ (t ++ u)) = List.cons _ (decChunkC len _ t) ++ u
    rw [ih, List.cons_append]

theorem charsOf_append : ∀ (L1 L2 : List (Nat × Nat)),
    charsOf (L1 ++ L2) = charsOf L1 ++ charsOf L2
  | [], L2 => rfl
  | (N, len) :: L1, L2 => by
    change decChunkC len N (charsOf (L1 ++ L2)) = decChunkC len N (charsOf L1) ++ charsOf L2
    rw [charsOf_append L1 L2, decChunkC_append]

theorem text_eq : CFSG.Monster.B.TText24.text = String.ofList (charsOf CFSG.KD.TBind24.CH) := by
  rw [CFSG.Monster.B.TText24.text, CFSG.KD.TBind24.C0.eq, CFSG.KD.TBind24.C1.eq,
    CFSG.KD.TBind24.C2.eq, CFSG.KD.TBind24.C3.eq, ← String.ofList_append, ← String.ofList_append,
    ← String.ofList_append, ← charsOf_append, ← charsOf_append, ← charsOf_append,
    CFSG.KD.TBind24.CH, CFSG.KD.TBind24.appP_eq, CFSG.KD.TBind24.appP_eq,
    CFSG.KD.TBind24.appP_eq, List.append_assoc, List.append_assoc]

theorem text_rows : ∀ k t : Nat, k < 4370 → t < 4416 →
    ((CFSG.Monster.B.Bin.b64Decode CFSG.Monster.B.TText24.text 2412256).get!
      (16 + 552 * k + t / 8)).toNat.testBit (t % 8) = (TR24 k).testBit t := by
  have hr : ∀ s < 69, rangeOK (dropP CFSG.KD.TBind24.CH (1 + 64 * s)) (64 * s)
      (CFSG.KC.BM.rowsS s) TR24 = true := by
    forall_lt_consts CFSG.KD.TBind24.r 69
  have hasc : asciiOK CFSG.KD.TBind24.CH = true := by
    rw [CFSG.KD.TBind24.CH, CFSG.KD.TBind24.appP_eq, CFSG.KD.TBind24.appP_eq,
      CFSG.KD.TBind24.appP_eq]
    exact asciiOK_append CFSG.KD.TBind24.asc0 (asciiOK_append CFSG.KD.TBind24.asc1
      (asciiOK_append CFSG.KD.TBind24.asc2 CFSG.KD.TBind24.asc3))
  rw [text_eq]
  exact b64Decode_rows hasc CFSG.KD.TBind24.len CFSG.KD.TBind24.hdr hr CFSG.KD.TBind24.last

theorem rowsMat_TR : CFSG.KC.BSeed.rowsMat 4370 TR24 =
    CFSG.KC.BM.stripMat CFSG.KC.BM.NativePair24.T :=
  CFSG.KC.BM.rowsMat_eq_stripMat (R := CFSG.KC.BM.NativePair24.T.rows)
    (S := CFSG.KC.BM.NativePair24.T) (by bm_blocks CFSG.KC.BM.NativePair24.rows_T 69)
    CFSG.KC.BM.NativePair24.wf_T

end CertificateChecks.KernelBM

end
