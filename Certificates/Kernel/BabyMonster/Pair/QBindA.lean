module

public import Certificates.Kernel.BabyMonster.Facts3101

public section

namespace CertificateChecks.KernelBM.Fix

open CFSG.KC.BM CFSG.KC.BM.Fix CFSG.KC.BSeed CFSG.KC.BM.Lat CFSG.KC.YModel CFSG.Monster.B.Dyadic

theorem quot1 : ∀ k < 4370, recOf FixedLine.Q1.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C1.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens1 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot1_ 69)

theorem rowsQ1 : rowsMat 4370 (recOf FixedLine.Q1.rows) = stripMat NativePair.Q1 := by
  have e : FixedLine.Q1.rows = NativePair.Q1.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q1.rows) (S := NativePair.Q1)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q1 69) NativePair24.wf_Q1

theorem qmat1 :
    Qmat 1 = stripMat NativePair.Q1 := (qmat_rows 1 quot1).trans rowsQ1

theorem quot2 : ∀ k < 4370, recOf FixedLine.Q2.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C2.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens2 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot2_ 69)

theorem rowsQ2 : rowsMat 4370 (recOf FixedLine.Q2.rows) = stripMat NativePair.Q2 := by
  have e : FixedLine.Q2.rows = NativePair.Q2.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q2.rows) (S := NativePair.Q2)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q2 69) NativePair24.wf_Q2

theorem qmat2 :
    Qmat 2 = stripMat NativePair.Q2 := (qmat_rows 2 quot2).trans rowsQ2

theorem quot3 : ∀ k < 4370, recOf FixedLine.Q3.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C3.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens3 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot3_ 69)

theorem rowsQ3 : rowsMat 4370 (recOf FixedLine.Q3.rows) = stripMat NativePair.Q3 := by
  have e : FixedLine.Q3.rows = NativePair.Q3.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q3.rows) (S := NativePair.Q3)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q3 69) NativePair24.wf_Q3

theorem qmat3 :
    Qmat 3 = stripMat NativePair.Q3 := (qmat_rows 3 quot3).trans rowsQ3

theorem quot4 : ∀ k < 4370, recOf FixedLine.Q4.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C4.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens4 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot4_ 69)

theorem rowsQ4 : rowsMat 4370 (recOf FixedLine.Q4.rows) = stripMat NativePair.Q4 := by
  have e : FixedLine.Q4.rows = NativePair.Q4.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q4.rows) (S := NativePair.Q4)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q4 69) NativePair24.wf_Q4

theorem qmat4 :
    Qmat 4 = stripMat NativePair.Q4 := (qmat_rows 4 quot4).trans rowsQ4

theorem quot5 : ∀ k < 4370, recOf FixedLine.Q5.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C5.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens5 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot5_ 69)

theorem rowsQ5 : rowsMat 4370 (recOf FixedLine.Q5.rows) = stripMat NativePair.Q5 := by
  have e : FixedLine.Q5.rows = NativePair.Q5.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q5.rows) (S := NativePair.Q5)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q5 69) NativePair24.wf_Q5

theorem qmat5 :
    Qmat 5 = stripMat NativePair.Q5 := (qmat_rows 5 quot5).trans rowsQ5

theorem quot6 : ∀ k < 4370, recOf FixedLine.Q6.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C6.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens6 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot6_ 69)

theorem rowsQ6 : rowsMat 4370 (recOf FixedLine.Q6.rows) = stripMat NativePair.Q6 := by
  have e : FixedLine.Q6.rows = NativePair.Q6.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q6.rows) (S := NativePair.Q6)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q6 69) NativePair24.wf_Q6

theorem qmat6 :
    Qmat 6 = stripMat NativePair.Q6 := (qmat_rows 6 quot6).trans rowsQ6

theorem quot7 : ∀ k < 4370, recOf FixedLine.Q7.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C7.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens7 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot7_ 69)

theorem rowsQ7 : rowsMat 4370 (recOf FixedLine.Q7.rows) = stripMat NativePair.Q7 := by
  have e : FixedLine.Q7.rows = NativePair.Q7.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q7.rows) (S := NativePair.Q7)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q7 69) NativePair24.wf_Q7

theorem qmat7 :
    Qmat 7 = stripMat NativePair.Q7 := (qmat_rows 7 quot7).trans rowsQ7

theorem quot8 : ∀ k < 4370, recOf FixedLine.Q8.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C8.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens8 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot8_ 69)

theorem rowsQ8 : rowsMat 4370 (recOf FixedLine.Q8.rows) = stripMat NativePair.Q8 := by
  have e : FixedLine.Q8.rows = NativePair.Q8.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q8.rows) (S := NativePair.Q8)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q8 69) NativePair24.wf_Q8

theorem qmat8 :
    Qmat 8 = stripMat NativePair.Q8 := (qmat_rows 8 quot8).trans rowsQ8

theorem quot9 : ∀ k < 4370, recOf FixedLine.Q9.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C9.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens9 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot9_ 69)

theorem rowsQ9 : rowsMat 4370 (recOf FixedLine.Q9.rows) = stripMat NativePair.Q9 := by
  have e : FixedLine.Q9.rows = NativePair.Q9.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q9.rows) (S := NativePair.Q9)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q9 69) NativePair24.wf_Q9

theorem qmat9 :
    Qmat 9 = stripMat NativePair.Q9 := (qmat_rows 9 quot9).trans rowsQ9

theorem quot10 : ∀ k < 4370, recOf FixedLine.Q10.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C10.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens10 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot10_ 69)

theorem rowsQ10 : rowsMat 4370 (recOf FixedLine.Q10.rows) = stripMat NativePair.Q10 := by
  have e : FixedLine.Q10.rows = NativePair.Q10.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q10.rows) (S := NativePair.Q10)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q10 69) NativePair24.wf_Q10

theorem qmat10 :
    Qmat 10 = stripMat NativePair.Q10 := (qmat_rows 10 quot10).trans rowsQ10

theorem quot11 : ∀ k < 4370, recOf FixedLine.Q11.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C11.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens11 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot11_ 69)

theorem rowsQ11 : rowsMat 4370 (recOf FixedLine.Q11.rows) = stripMat NativePair.Q11 := by
  have e : FixedLine.Q11.rows = NativePair.Q11.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q11.rows) (S := NativePair.Q11)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q11 69) NativePair24.wf_Q11

theorem qmat11 :
    Qmat 11 = stripMat NativePair.Q11 := (qmat_rows 11 quot11).trans rowsQ11

theorem quot12 : ∀ k < 4370, recOf FixedLine.Q12.rows k =
    projRow 1197 FixedLine.f (recOf FixedLine.C12.rows (if k < 1197 then k else k + 1)) :=
  quotOK_sound FixedLine.lens12 (by forall_lt_consts CFSG.KC.BM.FixedLine.quot12_ 69)

theorem rowsQ12 : rowsMat 4370 (recOf FixedLine.Q12.rows) = stripMat NativePair.Q12 := by
  have e : FixedLine.Q12.rows = NativePair.Q12.rows := rfl
  rw [e]
  exact rowsMat_eq_stripMat (R := NativePair.Q12.rows) (S := NativePair.Q12)
    (by bm_blocks CFSG.KC.BM.NativePair24.rows_Q12 69) NativePair24.wf_Q12

theorem qmat12 :
    Qmat 12 = stripMat NativePair.Q12 := (qmat_rows 12 quot12).trans rowsQ12

end CertificateChecks.KernelBM.Fix

end
