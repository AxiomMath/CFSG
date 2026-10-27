module

public import Certificates.Data.SmithB45MatM12Nor
import CFSG.Certificates.Kernel.B45M12Sound
import Certificates.Kernel.C260404.S44
import Certificates.Kernel.C260404.S144A
import Certificates.Kernel.C260404.S144B
import Certificates.Kernel.C260404.S230A
import Certificates.Kernel.C260404.S230B
import Certificates.Kernel.C260404.Q32
import Certificates.Kernel.C260404.N10
import Certificates.Kernel.C260404.N44
import Certificates.Kernel.C260404.N144
import Certificates.Kernel.C260404.F4

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12 FieldFour
  CFSG.KC.B45M12 CFSG.KD.C260404

namespace CertificateChecks.Kernel260404

theorem t44_eq : T44A = t44 arrA ∧ T44B = t44 arrB := by
  obtain ⟨-, -, -, h⟩ := subK_spec sub44
  refine ⟨?_, ?_⟩ <;> rw [t44]
  · exact (h _ _ (List.Mem.head _)).2.1
  · exact (h _ _ (List.Mem.tail _ (List.Mem.head _))).2.1

theorem K440_eq : K440 arrA = kronM 10 44 (cols10 arrA) T44A ∧
    K440 arrB = kronM 10 44 (cols10 arrB) T44B := by
  rw [K440, K440, t44_eq.1, t44_eq.2]
  exact ⟨rfl, rfl⟩

theorem t144_eq : T144A = t144 arrA ∧ T144B = t144 arrB := by
  obtain ⟨-, -, -, hA⟩ := subK_spec sub144A
  obtain ⟨-, -, -, hB⟩ := subK_spec sub144B
  refine ⟨?_, ?_⟩
  · rw [t144, K440_eq.1]
    exact (hA _ _ (List.Mem.head _)).2.1
  · rw [t144, K440_eq.2]
    exact (hB _ _ (List.Mem.head _)).2.1

theorem t230_eq : T230A = t230 arrA ∧ T230B = t230 arrB := by
  obtain ⟨-, -, -, hA⟩ := subK_spec sub230A
  obtain ⟨-, -, -, hB⟩ := subK_spec sub230B
  refine ⟨?_, ?_⟩
  · rw [t230, K440_eq.1]
    exact (hA _ _ (List.Mem.head _)).2.1
  · rw [t230, K440_eq.2]
    exact (hB _ _ (List.Mem.head _)).2.1

theorem t32_eq : T32A = t32 arrA ∧ T32B = t32 arrB := by
  obtain ⟨-, -, -, h⟩ := quotK_spec quot32
  refine ⟨?_, ?_⟩
  · rw [t32, ← t230_eq.1]
    exact (h _ _ (List.Mem.head _)).2.1
  · rw [t32, ← t230_eq.2]
    exact (h _ _ (List.Mem.tail _ (List.Mem.head _))).2.1

theorem length_t32 (a : Array ℕ) : (t32 a).length = 32 := by
  rw [t32, mulM, List.length_map, mulM, List.length_map, Bsel, List.length_map, List.length_range]

theorem untab_tab32F {a : Array ℕ} {T : List ℕ} (h : T = t32 a) :
    untab (tab32F a) = pairMat 32 32 (ofF2 T) := by
  rw [tab32F, untab_mapTab, untab_tab, pairMat_ofF2, h]

theorem untab_B16 : untab B16 = pairMat 32 16 B16c := by
  unfold B16 B16c
  exact untab_decF4_cols 32 16 B16Rows

theorem untab_P16 : untab P16 = pairMat 16 32 P16c := by
  unfold P16 P16c
  exact untab_decF4_cols 16 32 P16Rows

theorem length_g16 (T : List ℕ) : (g16 T).length = 16 := by
  rw [g16, mulF4, List.length_map, mulF4, List.length_map, B16c, colsF4, length_trF4]

theorem untab_tab16a {a : Array ℕ} {T : List ℕ} (h : T = t32 a) :
    untab (tab16a a) = pairMat 16 16 (g16 T) := by
  have hP : P16c.length ≤ 32 := by
    rw [P16c, colsF4]
    exact (length_trF4 32 _).le
  have hT : (ofF2 T).length ≤ 32 := by
    rw [ofF2, List.length_map, h]
    exact (length_t32 a).le
  rw [tab16a, untab_mulT, untab_mulT, untab_tab32F h, untab_B16, untab_P16, g16,
    pairMat_mulF4 (k := 32) _ _ hP, pairMat_mulF4 (k := 32) _ _ hT, Matrix.mul_assoc]

theorem untab_tab16b {a : Array ℕ} {T : List ℕ} (h : T = t32 a) :
    untab (tab16b a) = pairMat 16 16 (frobF4 (g16 T)) := by
  rw [tab16b, untab_mapTab, untab_tab16a h, pairMat_frobF4]

theorem length_frob_g16 (T : List ℕ) : (frobF4 (g16 T)).length = 16 := by
  rw [frobF4, List.length_map, length_g16]

end CertificateChecks.Kernel260404

public section

namespace Certificates

open CertificateChecks.Kernel260404

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12 FieldFour in
theorem certificate260404 :
    subOKM 100 44 (K100 arrA) (K100 arrB) B44 P44 = true ∧
    P44.all (· < 2 ^ 44) = true ∧
    subOKM 440 144 (K440 arrA) (K440 arrB) B144 P144 = true ∧
    subOKM 440 230 (K440 arrA) (K440 arrB) B230 P230 = true ∧
    quotOKM 230 32 (t230 arrA) (t230 arrB) Bsel Psel = true ∧
    subOK (tab32F arrA) (tab32F arrB) B16 P16 = true ∧
    c10.check (tab10 arrA) (tab10 arrB) = true ∧
    c44.check (tab44 arrA) (tab44 arrB) = true ∧
    c144.check (tab144 arrA) (tab144 arrB) = true ∧
    c16a.check (tab16a arrA) (tab16a arrB) = true ∧
    c16b.check (tab16b arrA) (tab16b arrB) = true ∧
    Matrix.trace (untab (mulT (tab16a arrA) (tab16a arrB))) = ω ∧
    Matrix.trace (untab (mulT (tab16b arrA) (tab16b arrB))) = ω₂ := by
  obtain ⟨hs16, hn16a, hn16b, htr16a, htr16b⟩ := f4
  have hsub144 : subOKM 440 144 (K440 arrA) (K440 arrB) B144 P144 = true := by
    rw [K440_eq.1, K440_eq.2]
    exact subOKM_of_subK sub144A sub144B (List.Mem.head _) (List.Mem.head _)
  have hsub230 : subOKM 440 230 (K440 arrA) (K440 arrB) B230 P230 = true := by
    rw [K440_eq.1, K440_eq.2]
    exact subOKM_of_subK sub230A sub230B (List.Mem.head _) (List.Mem.head _)
  have hquot32 : quotOKM 230 32 (t230 arrA) (t230 arrB) Bsel Psel = true := by
    rw [← t230_eq.1, ← t230_eq.2]
    exact quotOKM_of_quotK quot32 quot32 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _))
  have hsub16 : subOK (tab32F arrA) (tab32F arrB) B16 P16 = true :=
    subOK_of_subF4 (untab_tab32F t32_eq.1) (untab_tab32F t32_eq.2) untab_B16 untab_P16 hs16
      (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _))
  have hnor10 : c10.check (tab10 arrA) (tab10 arrB) = true :=
    norF2_sound (Ga := cols10 arrA) (Gb := cols10 arrB) (by rw [tab10, untab_tab])
      (by rw [tab10, untab_tab]) nor10
  have hnor44 : c44.check (tab44 arrA) (tab44 arrB) = true :=
    norF2_sound (Ga := T44A) (Gb := T44B) (by rw [tab44, untab_tab, t44_eq.1])
      (by rw [tab44, untab_tab, t44_eq.2]) nor44
  have hnor144 : c144.check (tab144 arrA) (tab144 arrB) = true :=
    norF2_sound (Ga := T144A) (Gb := T144B) (by rw [tab144, untab_tab, t144_eq.1])
      (by rw [tab144, untab_tab, t144_eq.2]) nor144
  have hnor16a : c16a.check (tab16a arrA) (tab16a arrB) = true :=
    norF4_sound (untab_tab16a t32_eq.1) (untab_tab16a t32_eq.2) hn16a
  have hnor16b : c16b.check (tab16b arrA) (tab16b arrB) = true :=
    norF4_sound (untab_tab16b t32_eq.1) (untab_tab16b t32_eq.2) hn16b
  have htrace16a : Matrix.trace (untab (mulT (tab16a arrA) (tab16a arrB))) = ω := by
    rw [untab_mulT, untab_tab16a t32_eq.1, untab_tab16a t32_eq.2,
      ← pairMat_mulF4 (k := 16) _ _ (length_g16 T32A).le, traceK_sound htr16a]
    rfl
  have htrace16b : Matrix.trace (untab (mulT (tab16b arrA) (tab16b arrB))) = ω₂ := by
    rw [untab_mulT, untab_tab16b t32_eq.1, untab_tab16b t32_eq.2,
      ← pairMat_mulF4 (k := 16) _ _ (length_frob_g16 T32A).le, traceK_sound htr16b]
    rfl
  exact ⟨subOKM_of_subK sub44 sub44 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)),
    bound44, hsub144, hsub230, hquot32, hsub16, hnor10, hnor44, hnor144, hnor16a, hnor16b,
    htrace16a, htrace16b⟩

end Certificates

end
