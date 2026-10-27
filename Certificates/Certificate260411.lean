module

public import Certificates.Data.SmithB45J2Nor
import CFSG.Certificates.Kernel.B45J2Sound
import Certificates.Kernel.C260411.S14
import Certificates.Kernel.C260411.S64
import Certificates.Kernel.C260411.S160A
import Certificates.Kernel.C260411.S160B
import Certificates.Kernel.C260411.NSmall
import Certificates.Kernel.C260411.N64
import Certificates.Kernel.C260411.N84
import Certificates.Kernel.C260411.N160

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.J2Mod FieldFour
  CFSG.KC.B45M12 CFSG.KC.B45J2 CFSG.KD.C260411

namespace CertificateChecks.Kernel260411

theorem len_A6 : A6.length = 6 := by
  rw [A6, colsF4, length_trF4]

theorem len_B6 : B6.length = 6 := by
  rw [B6, colsF4, length_trF4]

theorem len_frob (X : List (ℕ × ℕ)) : (frobF4 X).length = X.length := by
  rw [frobF4, List.length_map]

theorem untab_tA6 : untab tA6 = pairMat 6 6 A6 := by
  rw [tA6, A6]
  exact untab_decF4J 6 6 tA6Rows

theorem untab_tB6 : untab tB6 = pairMat 6 6 B6 := by
  rw [tB6, B6]
  exact untab_decF4J 6 6 tB6Rows

theorem untab_B14 : untab B14 = pairMat 36 14 B14c := by
  rw [B14, B14c]
  exact untab_decF4L 36 14 B14Limbs

theorem untab_P14 : untab P14 = pairMat 14 36 P14c := by
  rw [P14, P14c]
  exact untab_decF4L 14 36 P14Limbs

theorem untab_B64 : untab B64 = pairMat 84 64 B64c := by
  rw [B64, B64c]
  exact untab_decF4L 84 64 B64Limbs

theorem untab_P64 : untab P64 = pairMat 64 84 P64c := by
  rw [P64, P64c]
  exact untab_decF4L 64 84 P64Limbs

theorem untab_B160 : untab B160 = pairMat 196 160 B160c := by
  rw [B160, B160c]
  exact untab_decF4L 196 160 B160Limbs

theorem untab_P160 : untab P160 = pairMat 160 196 P160c := by
  rw [P160, P160c]
  exact untab_decF4L 160 196 P160Limbs

theorem untab_kron {m n : ℕ} {Ka : Vector (Vector FieldFour m) m}
    {Kb : Vector (Vector FieldFour n) n} {A B : List (ℕ × ℕ)} (ha : untab Ka = pairMat m m A)
    (hb : untab Kb = pairMat n n B) (hA : A.length = m) (hB : B.length = n) :
    untab (kronTab Ka Kb) = pairMat (m * n) (m * n) (kronF4 m n A B) := by
  rw [untab_kronTab, ha, hb, pairMat_kronF4 hA hB]

theorem untab_frob {n : ℕ} {K : Vector (Vector FieldFour n) n} {A : List (ℕ × ℕ)}
    (h : untab K = pairMat n n A) : untab (mapTab frob K) = pairMat n n (frobF4 A) := by
  rw [untab_mapTab, h, pairMat_frobF4]

theorem untab_tAA : untab tAA = pairMat (6 * 6) (6 * 6) (kronF4 6 6 A6 A6) := by
  rw [tAA]
  exact untab_kron untab_tA6 untab_tA6 len_A6 len_A6

theorem untab_tBB : untab tBB = pairMat (6 * 6) (6 * 6) (kronF4 6 6 B6 B6) := by
  rw [tBB]
  exact untab_kron untab_tB6 untab_tB6 len_B6 len_B6

theorem len_T14A : T14A.length = 14 :=
  ((subKF4_spec sub14).2 _ _ (List.Mem.head _)).2.1

theorem len_T14B : T14B.length = 14 :=
  ((subKF4_spec sub14).2 _ _ (List.Mem.tail _ (List.Mem.head _))).2.1

theorem untab_t14A : untab t14A = pairMat 14 14 T14A := by
  rw [t14A, untab_mulT, untab_mulT, untab_P14, untab_tAA, untab_B14]
  exact ((subKF4_spec sub14).2 _ _ (List.Mem.head _)).2.2.1.symm

theorem untab_t14B : untab t14B = pairMat 14 14 T14B := by
  rw [t14B, untab_mulT, untab_mulT, untab_P14, untab_tBB, untab_B14]
  exact ((subKF4_spec sub14).2 _ _ (List.Mem.tail _ (List.Mem.head _))).2.2.1.symm

theorem untab_tA14 : untab tA14 = pairMat (6 * 14) (6 * 14) (kronF4 6 14 A6 T14A) := by
  rw [tA14]
  exact untab_kron untab_tA6 untab_t14A len_A6 len_T14A

theorem untab_tB14 : untab tB14 = pairMat (6 * 14) (6 * 14) (kronF4 6 14 B6 T14B) := by
  rw [tB14]
  exact untab_kron untab_tB6 untab_t14B len_B6 len_T14B

theorem len_T64A : T64A.length = 64 :=
  ((subKF4_spec sub64).2 _ _ (List.Mem.head _)).2.1

theorem len_T64B : T64B.length = 64 :=
  ((subKF4_spec sub64).2 _ _ (List.Mem.tail _ (List.Mem.head _))).2.1

theorem untab_t64A : untab t64A = pairMat 64 64 T64A := by
  rw [t64A, untab_mulT, untab_mulT, untab_P64, untab_tA14, untab_B64]
  exact ((subKF4_spec sub64).2 _ _ (List.Mem.head _)).2.2.1.symm

theorem untab_t64B : untab t64B = pairMat 64 64 T64B := by
  rw [t64B, untab_mulT, untab_mulT, untab_P64, untab_tB14, untab_B64]
  exact ((subKF4_spec sub64).2 _ _ (List.Mem.tail _ (List.Mem.head _))).2.2.1.symm

theorem untab_t14bA : untab t14bA = pairMat 14 14 (frobF4 T14A) := by
  rw [t14bA]
  exact untab_frob untab_t14A

theorem untab_t14bB : untab t14bB = pairMat 14 14 (frobF4 T14B) := by
  rw [t14bB]
  exact untab_frob untab_t14B

theorem untab_tAAb :
    untab tAAb = pairMat (14 * 14) (14 * 14) (kronF4 14 14 T14A (frobF4 T14A)) := by
  rw [tAAb]
  exact untab_kron untab_t14A untab_t14bA len_T14A ((len_frob _).trans len_T14A)

theorem untab_tBBb :
    untab tBBb = pairMat (14 * 14) (14 * 14) (kronF4 14 14 T14B (frobF4 T14B)) := by
  rw [tBBb]
  exact untab_kron untab_t14B untab_t14bB len_T14B ((len_frob _).trans len_T14B)

theorem untab_t160A : untab t160A = pairMat 160 160 T160A := by
  rw [t160A, untab_mulT, untab_mulT, untab_P160, untab_tAAb, untab_B160]
  exact ((subKF4_spec sub160A).2 _ _ (List.Mem.head _)).2.2.1.symm

theorem untab_t160B : untab t160B = pairMat 160 160 T160B := by
  rw [t160B, untab_mulT, untab_mulT, untab_P160, untab_tBBb, untab_B160]
  exact ((subKF4_spec sub160B).2 _ _ (List.Mem.head _)).2.2.1.symm

theorem untab_t36A : untab t36A = pairMat (6 * 6) (6 * 6) (kronF4 6 6 A6 (frobF4 A6)) := by
  rw [t36A]
  exact untab_kron untab_tA6 (untab_frob untab_tA6) len_A6 ((len_frob _).trans len_A6)

theorem untab_t36B : untab t36B = pairMat (6 * 6) (6 * 6) (kronF4 6 6 B6 (frobF4 B6)) := by
  rw [t36B]
  exact untab_kron untab_tB6 (untab_frob untab_tB6) len_B6 ((len_frob _).trans len_B6)

theorem untab_t84A :
    untab t84A = pairMat (6 * 14) (6 * 14) (kronF4 6 14 A6 (frobF4 T14A)) := by
  rw [t84A]
  exact untab_kron untab_tA6 untab_t14bA len_A6 ((len_frob _).trans len_T14A)

theorem untab_t84B :
    untab t84B = pairMat (6 * 14) (6 * 14) (kronF4 6 14 B6 (frobF4 T14B)) := by
  rw [t84B]
  exact untab_kron untab_tB6 untab_t14bB len_B6 ((len_frob _).trans len_T14B)

instance : NeZero (6 * 6) := ⟨by norm_num⟩

instance : NeZero (6 * 14) := ⟨by norm_num⟩

end CertificateChecks.Kernel260411

public section

namespace Certificates

open CertificateChecks.Kernel260411

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.J2Mod FieldFour in
theorem certificate260411 :
    CFSG.Quasithin.B45Mat.subOK tAA tBB B14 P14 = true ∧
    CFSG.Quasithin.B45Mat.subOK tA14 tB14 B64 P64 = true ∧
    CFSG.Quasithin.B45Mat.subOK tAAb tBBb B160 P160 = true ∧
    c6.check tA6 tB6 = true ∧
    c14.check t14A t14B = true ∧
    c36.check t36A t36B = true ∧
    c64.check t64A t64B = true ∧
    c84.check t84A t84B = true ∧
    c160.check t160A t160B = true ∧
    Matrix.trace (untab (CFSG.Quasithin.B45Mat.wordT tA6 tB6 tw6)) = ω ∧
    Matrix.trace (untab (CFSG.Quasithin.B45Mat.wordT t14A t14B tw14)) = ω₂ ∧
    Matrix.trace (untab (CFSG.Quasithin.B45Mat.wordT t64A t64B tw64)) = ω₂ := by
  obtain ⟨tr6, tr14⟩ := trace6_14
  have h14 : subOK tAA tBB B14 P14 = true :=
    subOK_of_subKF4 untab_tAA untab_tBB untab_B14 untab_P14 sub14 (List.Mem.head _)
      (List.Mem.tail _ (List.Mem.head _))
  have h64 : subOK tA14 tB14 B64 P64 = true :=
    subOK_of_subKF4 untab_tA14 untab_tB14 untab_B64 untab_P64 sub64 (List.Mem.head _)
      (List.Mem.tail _ (List.Mem.head _))
  have h160 : subOK tAAb tBBb B160 P160 = true := by
    simp only [subOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
      Bool.and_true]
    have hA := subOK_of_subKF4 untab_tAAb untab_tAAb untab_B160 untab_P160 sub160A
      (List.Mem.head _) (List.Mem.head _)
    have hB := subOK_of_subKF4 untab_tBBb untab_tBBb untab_B160 untab_P160 sub160B
      (List.Mem.head _) (List.Mem.head _)
    simp only [subOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
      Bool.and_true] at hA hB
    exact ⟨hA.1, hA.2.1, hB.2.2⟩
  have n6 : c6.check tA6 tB6 = true := norL_sound untab_tA6 untab_tB6 nor6
  have n14 : c14.check t14A t14B = true := norL_sound untab_t14A untab_t14B nor14
  have n36 : c36.check t36A t36B = true := norL_sound untab_t36A untab_t36B nor36
  have n64 : c64.check t64A t64B = true := norL_sound untab_t64A untab_t64B nor64
  have n84 : c84.check t84A t84B = true := norL_sound untab_t84A untab_t84B nor84
  have n160 : c160.check t160A t160B = true := norL_sound untab_t160A untab_t160B nor160
  have t6 : Matrix.trace (untab (wordT tA6 tB6 tw6)) = ω := by
    rw [untab_wordT_eq untab_tA6 untab_tB6 len_A6.le len_B6.le, traceK_sound tr6]
    rfl
  have t14 : Matrix.trace (untab (wordT t14A t14B tw14)) = ω₂ := by
    rw [untab_wordT_eq untab_t14A untab_t14B len_T14A.le len_T14B.le, traceK_sound tr14]
    rfl
  have t64 : Matrix.trace (untab (wordT t64A t64B tw64)) = ω₂ := by
    rw [untab_wordT_eq untab_t64A untab_t64B len_T64A.le len_T64B.le, traceK_sound trace64]
    rfl
  exact ⟨h14, h64, h160, n6, n14, n36, n64, n84, n160, t6, t14, t64⟩

end Certificates
