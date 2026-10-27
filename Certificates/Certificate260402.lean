module

public import Certificates.Data.SmithB45MatM22Nor
import CFSG.Certificates.Kernel.B45M22Sound
import Certificates.Kernel.C260402.Cols
import Certificates.Kernel.C260402.Len
import Certificates.Kernel.C260402.S34
import Certificates.Kernel.C260402.S99
import Certificates.Kernel.C260402.Q98
import Certificates.Kernel.C260402.S70aA
import Certificates.Kernel.C260402.S70aB
import Certificates.Kernel.C260402.PinP
import Certificates.Kernel.C260402.Frob
import Certificates.Kernel.C260402.N10
import Certificates.Kernel.C260402.N34
import Certificates.Kernel.C260402.N98
import Certificates.Kernel.C260402.N70a
import Certificates.Kernel.C260402.N70b
import Certificates.Kernel.C260402.Tr7
import Certificates.Kernel.C260402.Tr70a

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M22
  CFSG.Sporadic.Mathieu FieldFour CFSG.KC.B45M12 CFSG.KC.B45M22 CFSG.KD.C260402

namespace CertificateChecks.Kernel260402

theorem untab_B34 : untab B34 = maskMat 100 34 (trM 34 B34Rows) := untab_decF2_cols 100 34 _

theorem untab_P34 : untab P34 = maskMat 34 100 (trM 100 P34Rows) := untab_decF2_cols 34 100 _

theorem untab_B99 : untab B99 = maskMat 100 99 (trM 99 B99Rows) := untab_decF2_cols 100 99 _

theorem untab_P99 : untab P99 = maskMat 99 100 (trM 100 P99Rows) := untab_decF2_cols 99 100 _

theorem untab_B98 : untab B98 = maskMat 99 98 (trM 98 B98Rows) := untab_decF2_cols 99 98 _

theorem untab_P98 : untab P98 = maskMat 98 99 (trM 99 P98Rows) := untab_decF2_cols 98 99 _

theorem untab_B70a : untab B70a = pairMat 340 70 (colsD 70 7 B70aRows) :=
  untab_decF4_colsD (by norm_num) _

theorem untab_P70a : untab P70a = pairMat 70 340 (ofF2 P70aC) :=
  untab_decF4_of_eqF4 (k := 9) (by norm_num) pinP70a

theorem untab_tab34A : untab (tab34 m22a) = maskMat 34 34 T34A :=
  untab_mulT_of_subK (untab_kronBB cols10bA) untab_B34 untab_P34 sub34 (List.Mem.head _)

theorem untab_tab34B : untab (tab34 m22b) = maskMat 34 34 T34B :=
  untab_mulT_of_subK (untab_kronBB cols10bB) untab_B34 untab_P34 sub34
    (List.Mem.tail _ (List.Mem.head _))

theorem untab_tab34G11 : untab (tab34 g11) = maskMat 34 34 T34G11 :=
  untab_mulT_of_subK (untab_kronBB cols10bG11) untab_B34 untab_P34 sub34
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem untab_tab99A : untab (tab99 m22a) = maskMat 99 99 T99A :=
  untab_mulT_of_subK (untab_kronAB cols10aA cols10bA) untab_B99 untab_P99 sub99 (List.Mem.head _)

theorem untab_tab99B : untab (tab99 m22b) = maskMat 99 99 T99B :=
  untab_mulT_of_subK (untab_kronAB cols10aB cols10bB) untab_B99 untab_P99 sub99
    (List.Mem.tail _ (List.Mem.head _))

theorem untab_tab98A : untab (tab98 m22a) = maskMat 98 98 T98A :=
  untab_mulT_of_quotK untab_tab99A untab_B98 untab_P98 quot98 (List.Mem.head _)

theorem untab_tab98B : untab (tab98 m22b) = maskMat 98 98 T98B :=
  untab_mulT_of_quotK untab_tab99B untab_B98 untab_P98 quot98 (List.Mem.tail _ (List.Mem.head _))

theorem untab_tab340A : untab (tab340 m22a) = pairMat (10 * 34) (10 * 34) (k340 C10bA T34A) :=
  untab_tab340 (untab_tab10b cols10bA) untab_tab34A (length_of_colsK cols10bA) len34.1

theorem untab_tab340B : untab (tab340 m22b) = pairMat (10 * 34) (10 * 34) (k340 C10bB T34B) :=
  untab_tab340 (untab_tab10b cols10bB) untab_tab34B (length_of_colsK cols10bB) len34.2.1

theorem untab_tab340G11 :
    untab (tab340 g11) = pairMat (10 * 34) (10 * 34) (k340 C10bG11 T34G11) :=
  untab_tab340 (untab_tab10b cols10bG11) untab_tab34G11 (length_of_colsK cols10bG11) len34.2.2

theorem untab_tab70aA : untab (tab70a m22a) = pairMat 70 70 T70aA :=
  untab_mulT_of_subF4K untab_tab340A untab_B70a untab_P70a sub70aA (List.Mem.head _)

theorem untab_tab70aB : untab (tab70a m22b) = pairMat 70 70 T70aB :=
  untab_mulT_of_subF4K untab_tab340B untab_B70a untab_P70a sub70aB (List.Mem.head _)

theorem untab_B70b : untab B70b = (untab B70a).map frob := by
  rw [B70b, B70a, untab_decF4_deint (k := 7) (by norm_num) B70bRows,
    untab_decF4_deint (k := 7) (by norm_num) B70aRows, pairMat_eq_of_eqF4 frobB70,
    pairMat_frobF4, Matrix.transpose_map]

theorem untab_P70b : untab P70b = (untab P70a).map frob := by
  have h : P70b = P70a := by rw [P70b, P70a, P70b_rows]
  rw [h, untab_P70a, pairMat_ofF2]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, frob_ofPrime]

theorem untab_tab70b (g : G22) : untab (tab70b g) = (untab (tab70a g)).map frob := by
  rw [tab70b, tab70a]
  exact untab_mulT_frob (map_frob_tab340 g) untab_B70b untab_P70b

theorem untab_tab70bA : untab (tab70b m22a) = pairMat 70 70 (frobF4 T70aA) := by
  rw [untab_tab70b, untab_tab70aA, pairMat_frobF4]

theorem untab_tab70bB : untab (tab70b m22b) = pairMat 70 70 (frobF4 T70aB) := by
  rw [untab_tab70b, untab_tab70aB, pairMat_frobF4]

theorem trace_tab70a_g11 : Matrix.trace (untab (tab70a g11)) = ω := by
  have hK : (k340 C10bG11 T34G11).length ≤ 10 * 34 :=
    (length_k340 (length_of_colsK cols10bG11) len34.2.2).le
  have hP : (ofF2 P70aC).length ≤ 10 * 34 := by
    rw [length_ofF2, lenP70a]
  rw [tab70a, untab_mulT_mulT_F4 untab_tab340G11 untab_B70a untab_P70a hK hP,
    traceK_sound trace70a]
  rfl

end CertificateChecks.Kernel260402

public section

namespace Certificates

open CertificateChecks.Kernel260402

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M22
  CFSG.Sporadic.Mathieu FieldFour in
theorem certificate260402 :
    subOK (kronBB m22a) (kronBB m22b) B34 P34 = true ∧
    subOK (kronAB m22a) (kronAB m22b) B99 P99 = true ∧
    quotOK (tab99 m22a) (tab99 m22b) B98 P98 = true ∧
    subOK (tab340 m22a) (tab340 m22b) B70a P70a = true ∧
    subOK (tab340 m22a) (tab340 m22b) B70b P70b = true ∧
    c10a.check (tab10a m22a) (tab10a m22b) = true ∧
    c10b.check (tab10b m22a) (tab10b m22b) = true ∧
    c34.check (tab34 m22a) (tab34 m22b) = true ∧
    c98.check (tab98 m22a) (tab98 m22b) = true ∧
    c70a.check (tab70a m22a) (tab70a m22b) = true ∧
    c70b.check (tab70b m22a) (tab70b m22b) = true ∧
    Matrix.trace (untab (tab10a g7)) = 0 ∧
    Matrix.trace (untab (tab10b g7)) = 1 ∧
    Matrix.trace (untab (tab70a g11)) = ω ∧
    Matrix.trace (untab (tab70b g11)) = ω₂ := by
  have hsub34 : subOK (kronBB m22a) (kronBB m22b) B34 P34 = true :=
    subOK_of_subOKM (untab_kronBB cols10bA) (untab_kronBB cols10bB) untab_B34 untab_P34
      (subOKM_of_subK sub34 sub34 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)))
  have hsub99 : subOK (kronAB m22a) (kronAB m22b) B99 P99 = true :=
    subOK_of_subOKM (untab_kronAB cols10aA cols10bA) (untab_kronAB cols10aB cols10bB) untab_B99
      untab_P99 (subOKM_of_subK sub99 sub99 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)))
  have hquot98 : quotOK (tab99 m22a) (tab99 m22b) B98 P98 = true :=
    quotOK_of_quotOKM untab_tab99A untab_tab99B untab_B98 untab_P98
      (quotOKM_of_quotK quot98 quot98 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)))
  have hsub70a : subOK (tab340 m22a) (tab340 m22b) B70a P70a = true :=
    subOK_of_subF4K untab_tab340A untab_tab340B untab_B70a untab_P70a sub70aA sub70aB
      (List.Mem.head _) (List.Mem.head _)
  have hsub70b : subOK (tab340 m22a) (tab340 m22b) B70b P70b = true :=
    subOK_frob (map_frob_tab340 _) (map_frob_tab340 _) untab_B70b untab_P70b hsub70a
  have hnor10a : c10a.check (tab10a m22a) (tab10a m22b) = true :=
    norF2_sound' (untab_tab10a cols10aA) (untab_tab10a cols10aB) nor10a
  have hnor10b : c10b.check (tab10b m22a) (tab10b m22b) = true :=
    norF2_sound' (untab_tab10b cols10bA) (untab_tab10b cols10bB) nor10b
  have hnor34 : c34.check (tab34 m22a) (tab34 m22b) = true :=
    norF2_sound' untab_tab34A untab_tab34B nor34
  have hnor98 : c98.check (tab98 m22a) (tab98 m22b) = true :=
    norF2_sound' untab_tab98A untab_tab98B nor98
  have hnor70a : c70a.check (tab70a m22a) (tab70a m22b) = true :=
    norF4_sound' untab_tab70aA untab_tab70aB nor70a
  have hnor70b : c70b.check (tab70b m22a) (tab70b m22b) = true :=
    norF4_sound' untab_tab70bA untab_tab70bB nor70b
  have htr10a : Matrix.trace (untab (tab10a g7)) = 0 := by
    rw [untab_tab10a cols10aG7]
    exact trace_maskMat_eq trace10a rfl
  have htr10b : Matrix.trace (untab (tab10b g7)) = 1 := by
    rw [untab_tab10b cols10bG7]
    exact trace_maskMat_eq trace10b rfl
  have htr70b : Matrix.trace (untab (tab70b g11)) = ω₂ := by
    rw [untab_tab70b, trace_map_frob, trace_tab70a_g11, frob_ω]
  exact ⟨hsub34, hsub99, hquot98, hsub70a, hsub70b, hnor10a, hnor10b, hnor34, hnor98, hnor70a,
    hnor70b, htr10a, htr10b, trace_tab70a_g11, htr70b⟩

end Certificates

end
