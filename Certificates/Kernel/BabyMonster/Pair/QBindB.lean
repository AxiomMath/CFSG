module

public import Certificates.Kernel.BabyMonster.Facts3101

public section

namespace CertificateChecks.KernelBM.Fix

open CFSG.KC.BM CFSG.KC.BM.Fix CFSG.KC.BSeed CFSG.KC.BM.Lat CFSG.KC.YModel CFSG.Monster.B.Dyadic

theorem quot13 : ∀ k < 4370, recOf FixedLine.Q13.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C13.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens13 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot13_ 69)

theorem rowsQ13 : rowsMat 4370 (recOf FixedLine.Q13.rows) = stripMat NativePair.Q13 := by
  have e : FixedLine.Q13.rows = NativePair.Q13.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q13.rows) (S := NativePair.Q13)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q13 69) NativePair24.wf_Q13

theorem qmat13 :
    Qmat 13 = stripMat NativePair.Q13 := (qmat_rows 13 quot13).trans rowsQ13

theorem quot14 : ∀ k < 4370, recOf FixedLine.Q14.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C14.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens14 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot14_ 69)

theorem rowsQ14 : rowsMat 4370 (recOf FixedLine.Q14.rows) = stripMat NativePair.Q14 := by
  have e : FixedLine.Q14.rows = NativePair.Q14.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q14.rows) (S := NativePair.Q14)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q14 69) NativePair24.wf_Q14

theorem qmat14 :
    Qmat 14 = stripMat NativePair.Q14 := (qmat_rows 14 quot14).trans rowsQ14

theorem quot15 : ∀ k < 4370, recOf FixedLine.Q15.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C15.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens15 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot15_ 69)

theorem rowsQ15 : rowsMat 4370 (recOf FixedLine.Q15.rows) = stripMat NativePair.Q15 := by
  have e : FixedLine.Q15.rows = NativePair.Q15.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q15.rows) (S := NativePair.Q15)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q15 69) NativePair24.wf_Q15

theorem qmat15 :
    Qmat 15 = stripMat NativePair.Q15 := (qmat_rows 15 quot15).trans rowsQ15

theorem quot16 : ∀ k < 4370, recOf FixedLine.Q16.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C16.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens16 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot16_ 69)

theorem rowsQ16 : rowsMat 4370 (recOf FixedLine.Q16.rows) = stripMat NativePair.Q16 := by
  have e : FixedLine.Q16.rows = NativePair.Q16.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q16.rows) (S := NativePair.Q16)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q16 69) NativePair24.wf_Q16

theorem qmat16 :
    Qmat 16 = stripMat NativePair.Q16 := (qmat_rows 16 quot16).trans rowsQ16

theorem quot17 : ∀ k < 4370, recOf FixedLine.Q17.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C17.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens17 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot17_ 69)

theorem rowsQ17 : rowsMat 4370 (recOf FixedLine.Q17.rows) = stripMat NativePair.Q17 := by
  have e : FixedLine.Q17.rows = NativePair.Q17.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q17.rows) (S := NativePair.Q17)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q17 69) NativePair24.wf_Q17

theorem qmat17 :
    Qmat 17 = stripMat NativePair.Q17 := (qmat_rows 17 quot17).trans rowsQ17

theorem quot18 : ∀ k < 4370, recOf FixedLine.Q18.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C18.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens18 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot18_ 69)

theorem rowsQ18 : rowsMat 4370 (recOf FixedLine.Q18.rows) = stripMat NativePair.Q18 := by
  have e : FixedLine.Q18.rows = NativePair.Q18.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q18.rows) (S := NativePair.Q18)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q18 69) NativePair24.wf_Q18

theorem qmat18 :
    Qmat 18 = stripMat NativePair.Q18 := (qmat_rows 18 quot18).trans rowsQ18

theorem quot19 : ∀ k < 4370, recOf FixedLine.Q19.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C19.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens19 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot19_ 69)

theorem rowsQ19 : rowsMat 4370 (recOf FixedLine.Q19.rows) = stripMat NativePair.Q19 := by
  have e : FixedLine.Q19.rows = NativePair.Q19.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q19.rows) (S := NativePair.Q19)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q19 69) NativePair24.wf_Q19

theorem qmat19 :
    Qmat 19 = stripMat NativePair.Q19 := (qmat_rows 19 quot19).trans rowsQ19

theorem quot20 : ∀ k < 4370, recOf FixedLine.Q20.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C20.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens20 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot20_ 69)

theorem rowsQ20 : rowsMat 4370 (recOf FixedLine.Q20.rows) = stripMat NativePair.Q20 := by
  have e : FixedLine.Q20.rows = NativePair.Q20.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q20.rows) (S := NativePair.Q20)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q20 69) NativePair24.wf_Q20

theorem qmat20 :
    Qmat 20 = stripMat NativePair.Q20 := (qmat_rows 20 quot20).trans rowsQ20

theorem quot21 : ∀ k < 4370, recOf FixedLine.Q21.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C21.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens21 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot21_ 69)

theorem rowsQ21 : rowsMat 4370 (recOf FixedLine.Q21.rows) = stripMat NativePair.Q21 := by
  have e : FixedLine.Q21.rows = NativePair.Q21.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q21.rows) (S := NativePair.Q21)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q21 69) NativePair24.wf_Q21

theorem qmat21 :
    Qmat 21 = stripMat NativePair.Q21 := (qmat_rows 21 quot21).trans rowsQ21

theorem quot22 : ∀ k < 4370, recOf FixedLine.Q22.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C22.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens22 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot22_ 69)

theorem rowsQ22 : rowsMat 4370 (recOf FixedLine.Q22.rows) = stripMat NativePair.Q22 := by
  have e : FixedLine.Q22.rows = NativePair.Q22.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q22.rows) (S := NativePair.Q22)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q22 69) NativePair24.wf_Q22

theorem qmat22 :
    Qmat 22 = stripMat NativePair.Q22 := (qmat_rows 22 quot22).trans rowsQ22

theorem quot23 : ∀ k < 4370, recOf FixedLine.Q23.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C23.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens23 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot23_ 69)

theorem rowsQ23 : rowsMat 4370 (recOf FixedLine.Q23.rows) = stripMat NativePair.Q23 := by
  have e : FixedLine.Q23.rows = NativePair.Q23.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q23.rows) (S := NativePair.Q23)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q23 69) NativePair24.wf_Q23

theorem qmat23 :
    Qmat 23 = stripMat NativePair.Q23 := (qmat_rows 23 quot23).trans rowsQ23

theorem quot24 : ∀ k < 4370, recOf FixedLine.Q24.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C24.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens24 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot24_ 69)

theorem rowsQ24 : rowsMat 4370 (recOf FixedLine.Q24.rows) = stripMat NativePair.Q24 := by
  have e : FixedLine.Q24.rows = NativePair.Q24.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q24.rows) (S := NativePair.Q24)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q24 69) NativePair24.wf_Q24

theorem qmat24 :
    Qmat 24 = stripMat NativePair.Q24 := (qmat_rows 24 quot24).trans rowsQ24

end CertificateChecks.KernelBM.Fix

end
