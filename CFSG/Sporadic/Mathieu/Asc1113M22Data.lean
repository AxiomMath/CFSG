module

public import CFSG.Sporadic.Mathieu.M22
public import Certificates.Certificate660104
public import Certificates.Certificate660105
public import Certificates.Certificate660106
public import Certificates.Certificate660109

public section

namespace CFSG.Sporadic.Mathieu.Asc1113M22

open CFSG.Mathieu.Asc1113M22
open CFSG.M23

abbrev H0 : Subgroup (Equiv.Perm (Fin 22)) := CFSG.Blueprint.NativeSporadic.M22

theorem closure_range_S2 : Subgroup.closure (Set.range S2) = H0 := by
  rw [show H0 = Subgroup.closure
      ({CFSG.Sporadic.Mathieu.m22gA, CFSG.Sporadic.Mathieu.m22gB} :
        Set (Equiv.Perm (Fin 22))) from rfl]
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

set_option maxRecDepth 10000 in
theorem z_sq : z * z = 1 := by decide

set_option maxRecDepth 10000 in
theorem z_ne_one : z ≠ 1 := by decide

set_option maxRecDepth 10000 in
theorem c1_eq_conj : c1 = g1 * z * g1⁻¹ := by decide
set_option maxRecDepth 10000 in
theorem c2_eq_conj : c2 = g2 * z * g2⁻¹ := by decide
set_option maxRecDepth 10000 in
theorem c3_eq_conj : c3 = g3 * z * g3⁻¹ := by decide
set_option maxRecDepth 10000 in
theorem c4_eq_conj : c4 = g4 * z * g4⁻¹ := by decide

@[expose] def Kz : Subgroup (Equiv.Perm (Fin 22)) := Subgroup.closure (Set.range C4)

theorem wordA_eval : evalGroupWord C4 wordA = S2 0 :=
  Certificates.certificate660104.1

theorem wordB_eval : evalGroupWord C4 wordB = S2 1 :=
  Certificates.certificate660104.2.1

theorem wordZ_eval : evalGroupWord S2 wordZ = z :=
  Certificates.certificate660104.2.2.1

theorem wordG1_eval : evalGroupWord S2 wordG1 = g1 :=
  Certificates.certificate660104.2.2.2.1

theorem wordG2_eval : evalGroupWord S2 wordG2 = g2 :=
  Certificates.certificate660104.2.2.2.2.1

theorem wordG3_eval : evalGroupWord S2 wordG3 = g3 :=
  Certificates.certificate660104.2.2.2.2.2.1

theorem wordG4_eval : evalGroupWord S2 wordG4 = g4 :=
  Certificates.certificate660104.2.2.2.2.2.2

theorem a_mem_Kz : S2 0 ∈ Kz := by
  rw [show S2 0 = evalGroupWord C4 wordA from wordA_eval.symm]
  exact evalGroupWord_mem_closure C4 wordA

theorem b_mem_Kz : S2 1 ∈ Kz := by
  rw [show S2 1 = evalGroupWord C4 wordB from wordB_eval.symm]
  exact evalGroupWord_mem_closure C4 wordB

theorem H0_le_Kz : H0 ≤ Kz := by
  rw [← closure_range_S2]
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i
  · exact a_mem_Kz
  · exact b_mem_Kz

theorem z_mem_H0 : z ∈ H0 := by
  rw [← closure_range_S2, ← wordZ_eval]
  exact evalGroupWord_mem_closure S2 wordZ

theorem g1_mem_H0 : g1 ∈ H0 := by
  rw [← closure_range_S2, ← wordG1_eval]
  exact evalGroupWord_mem_closure S2 wordG1

theorem g2_mem_H0 : g2 ∈ H0 := by
  rw [← closure_range_S2, ← wordG2_eval]
  exact evalGroupWord_mem_closure S2 wordG2

theorem g3_mem_H0 : g3 ∈ H0 := by
  rw [← closure_range_S2, ← wordG3_eval]
  exact evalGroupWord_mem_closure S2 wordG3

theorem g4_mem_H0 : g4 ∈ H0 := by
  rw [← closure_range_S2, ← wordG4_eval]
  exact evalGroupWord_mem_closure S2 wordG4

theorem Kz_le_H0 : Kz ≤ H0 := by
  rw [show Kz = Subgroup.closure (Set.range C4) from rfl]
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i
  · change c1 ∈ H0
    rw [c1_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g1_mem_H0 z_mem_H0) (Subgroup.inv_mem _ g1_mem_H0)
  · change c2 ∈ H0
    rw [c2_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g2_mem_H0 z_mem_H0) (Subgroup.inv_mem _ g2_mem_H0)
  · change c3 ∈ H0
    rw [c3_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g3_mem_H0 z_mem_H0) (Subgroup.inv_mem _ g3_mem_H0)
  · change c4 ∈ H0
    rw [c4_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g4_mem_H0 z_mem_H0) (Subgroup.inv_mem _ g4_mem_H0)

theorem Kz_eq_H0 : Kz = H0 := le_antisymm Kz_le_H0 H0_le_Kz

end CFSG.Sporadic.Mathieu.Asc1113M22

public section
namespace CFSG.Sporadic.Mathieu.Asc1113M22

open CFSG.Mathieu.Asc1113M22
open CFSG.M23

@[expose] def N0 : Subgroup (Equiv.Perm (Fin 22)) := Subgroup.closure (Set.range S3)

@[expose] def Kt : Subgroup (Equiv.Perm (Fin 22)) := Subgroup.closure (Set.range TC4)

set_option maxRecDepth 10000 in
theorem qt1_eq_conj : qt1 = tg1 * t * tg1⁻¹ := by decide
set_option maxRecDepth 10000 in
theorem qt2_eq_conj : qt2 = tg2 * t * tg2⁻¹ := by decide
set_option maxRecDepth 10000 in
theorem qt3_eq_conj : qt3 = tg3 * t * tg3⁻¹ := by decide
set_option maxRecDepth 10000 in
theorem qt4_eq_conj : qt4 = tg4 * t * tg4⁻¹ := by decide

theorem wordTA_eval : evalGroupWord TC4 wordTA = S3 0 :=
  Certificates.certificate660105.1

theorem wordTB_eval : evalGroupWord TC4 wordTB = S3 1 :=
  Certificates.certificate660105.2.1

theorem wordTU_eval : evalGroupWord TC4 wordTU = S3 2 :=
  Certificates.certificate660105.2.2.1

theorem wordTt_eval : evalGroupWord S3 wordTt = t :=
  Certificates.certificate660105.2.2.2.1

theorem wordTG1_eval : evalGroupWord S3 wordTG1 = tg1 :=
  Certificates.certificate660105.2.2.2.2.1

theorem wordTG2_eval : evalGroupWord S3 wordTG2 = tg2 :=
  Certificates.certificate660105.2.2.2.2.2.1

theorem wordTG3_eval : evalGroupWord S3 wordTG3 = tg3 :=
  Certificates.certificate660105.2.2.2.2.2.2.1

theorem wordTG4_eval : evalGroupWord S3 wordTG4 = tg4 :=
  Certificates.certificate660105.2.2.2.2.2.2.2

theorem a_mem_Kt : S3 0 ∈ Kt := by
  rw [show S3 0 = evalGroupWord TC4 wordTA from wordTA_eval.symm]
  exact evalGroupWord_mem_closure TC4 wordTA

theorem b_mem_Kt : S3 1 ∈ Kt := by
  rw [show S3 1 = evalGroupWord TC4 wordTB from wordTB_eval.symm]
  exact evalGroupWord_mem_closure TC4 wordTB

theorem u_mem_Kt : S3 2 ∈ Kt := by
  rw [show S3 2 = evalGroupWord TC4 wordTU from wordTU_eval.symm]
  exact evalGroupWord_mem_closure TC4 wordTU

theorem N0_le_Kt : N0 ≤ Kt := by
  rw [show N0 = Subgroup.closure (Set.range S3) from rfl]
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i
  · exact a_mem_Kt
  · exact b_mem_Kt
  · exact u_mem_Kt

theorem t_mem_N0 : t ∈ N0 := by
  rw [← wordTt_eval]
  exact evalGroupWord_mem_closure S3 wordTt

theorem tg1_mem_N0 : tg1 ∈ N0 := by
  rw [← wordTG1_eval]
  exact evalGroupWord_mem_closure S3 wordTG1

theorem tg2_mem_N0 : tg2 ∈ N0 := by
  rw [← wordTG2_eval]
  exact evalGroupWord_mem_closure S3 wordTG2

theorem tg3_mem_N0 : tg3 ∈ N0 := by
  rw [← wordTG3_eval]
  exact evalGroupWord_mem_closure S3 wordTG3

theorem tg4_mem_N0 : tg4 ∈ N0 := by
  rw [← wordTG4_eval]
  exact evalGroupWord_mem_closure S3 wordTG4

theorem Kt_le_N0 : Kt ≤ N0 := by
  rw [show Kt = Subgroup.closure (Set.range TC4) from rfl]
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i
  · change qt1 ∈ N0
    rw [qt1_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ tg1_mem_N0 t_mem_N0) (Subgroup.inv_mem _ tg1_mem_N0)
  · change qt2 ∈ N0
    rw [qt2_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ tg2_mem_N0 t_mem_N0) (Subgroup.inv_mem _ tg2_mem_N0)
  · change qt3 ∈ N0
    rw [qt3_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ tg3_mem_N0 t_mem_N0) (Subgroup.inv_mem _ tg3_mem_N0)
  · change qt4 ∈ N0
    rw [qt4_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ tg4_mem_N0 t_mem_N0) (Subgroup.inv_mem _ tg4_mem_N0)

theorem Kt_eq_N0 : Kt = N0 := le_antisymm Kt_le_N0 N0_le_Kt

end CFSG.Sporadic.Mathieu.Asc1113M22

public section
namespace CFSG.Sporadic.Mathieu.Asc1113M22

open CFSG.Mathieu.Asc1113M22
open CFSG.M23

@[expose] def Ku : Subgroup (Equiv.Perm (Fin 22)) := Subgroup.closure (Set.range UC4)

set_option maxRecDepth 10000 in
theorem qu1_eq_conj : qu1 = ug1 * u * ug1⁻¹ := by decide
set_option maxRecDepth 10000 in
theorem qu2_eq_conj : qu2 = ug2 * u * ug2⁻¹ := by decide
set_option maxRecDepth 10000 in
theorem qu3_eq_conj : qu3 = ug3 * u * ug3⁻¹ := by decide
set_option maxRecDepth 10000 in
theorem qu4_eq_conj : qu4 = ug4 * u * ug4⁻¹ := by decide

theorem wordUA_eval : evalGroupWord UC4 wordUA = S3 0 :=
  Certificates.certificate660106.1

theorem wordUB_eval : evalGroupWord UC4 wordUB = S3 1 :=
  Certificates.certificate660106.2.1

theorem wordUU_eval : evalGroupWord UC4 wordUU = S3 2 :=
  Certificates.certificate660106.2.2.1

theorem wordUu_eval : evalGroupWord S3 wordUu = u :=
  Certificates.certificate660106.2.2.2.1

theorem wordUG1_eval : evalGroupWord S3 wordUG1 = ug1 :=
  Certificates.certificate660106.2.2.2.2.1

theorem wordUG2_eval : evalGroupWord S3 wordUG2 = ug2 :=
  Certificates.certificate660106.2.2.2.2.2.1

theorem wordUG3_eval : evalGroupWord S3 wordUG3 = ug3 :=
  Certificates.certificate660106.2.2.2.2.2.2.1

theorem wordUG4_eval : evalGroupWord S3 wordUG4 = ug4 :=
  Certificates.certificate660106.2.2.2.2.2.2.2

theorem a_mem_Ku : S3 0 ∈ Ku := by
  rw [show S3 0 = evalGroupWord UC4 wordUA from wordUA_eval.symm]
  exact evalGroupWord_mem_closure UC4 wordUA

theorem b_mem_Ku : S3 1 ∈ Ku := by
  rw [show S3 1 = evalGroupWord UC4 wordUB from wordUB_eval.symm]
  exact evalGroupWord_mem_closure UC4 wordUB

theorem u_mem_Ku : S3 2 ∈ Ku := by
  rw [show S3 2 = evalGroupWord UC4 wordUU from wordUU_eval.symm]
  exact evalGroupWord_mem_closure UC4 wordUU

theorem N0_le_Ku : N0 ≤ Ku := by
  rw [show N0 = Subgroup.closure (Set.range S3) from rfl]
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i
  · exact a_mem_Ku
  · exact b_mem_Ku
  · exact u_mem_Ku

theorem u_mem_N0 : u ∈ N0 := by
  rw [← wordUu_eval]
  exact evalGroupWord_mem_closure S3 wordUu

theorem ug1_mem_N0 : ug1 ∈ N0 := by
  rw [← wordUG1_eval]
  exact evalGroupWord_mem_closure S3 wordUG1

theorem ug2_mem_N0 : ug2 ∈ N0 := by
  rw [← wordUG2_eval]
  exact evalGroupWord_mem_closure S3 wordUG2

theorem ug3_mem_N0 : ug3 ∈ N0 := by
  rw [← wordUG3_eval]
  exact evalGroupWord_mem_closure S3 wordUG3

theorem ug4_mem_N0 : ug4 ∈ N0 := by
  rw [← wordUG4_eval]
  exact evalGroupWord_mem_closure S3 wordUG4

theorem Ku_le_N0 : Ku ≤ N0 := by
  rw [show Ku = Subgroup.closure (Set.range UC4) from rfl]
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i
  · change qu1 ∈ N0
    rw [qu1_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ug1_mem_N0 u_mem_N0) (Subgroup.inv_mem _ ug1_mem_N0)
  · change qu2 ∈ N0
    rw [qu2_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ug2_mem_N0 u_mem_N0) (Subgroup.inv_mem _ ug2_mem_N0)
  · change qu3 ∈ N0
    rw [qu3_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ug3_mem_N0 u_mem_N0) (Subgroup.inv_mem _ ug3_mem_N0)
  · change qu4 ∈ N0
    rw [qu4_eq_conj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ug4_mem_N0 u_mem_N0) (Subgroup.inv_mem _ ug4_mem_N0)

theorem Ku_eq_N0 : Ku = N0 := le_antisymm Ku_le_N0 N0_le_Ku

end CFSG.Sporadic.Mathieu.Asc1113M22

end

public section
namespace CFSG.Sporadic.Mathieu.Asc1113M22

open CFSG.Mathieu.Asc1113M22
open CFSG.M23

theorem uU_sq : u * u = 1 :=
  Certificates.certificate660109.1

theorem uUAU_eval : evalGroupWord S2 wordUAU = u * S2 0 * u⁻¹ :=
  Certificates.certificate660109.2.1

theorem uUBU_eval : evalGroupWord S2 wordUBU = u * S2 1 * u⁻¹ :=
  Certificates.certificate660109.2.2

theorem u_conj_a_mem : u * S2 0 * u⁻¹ ∈ H0 := by
  rw [← uUAU_eval, ← closure_range_S2]
  exact evalGroupWord_mem_closure S2 wordUAU

theorem u_conj_b_mem : u * S2 1 * u⁻¹ ∈ H0 := by
  rw [← uUBU_eval, ← closure_range_S2]
  exact evalGroupWord_mem_closure S2 wordUBU

theorem u_conj_mem {x : Equiv.Perm (Fin 22)} (hx : x ∈ H0) : u * x * u⁻¹ ∈ H0 := by
  have hx' : x ∈ Subgroup.closure
      ({CFSG.Sporadic.Mathieu.m22gA, CFSG.Sporadic.Mathieu.m22gB} :
        Set (Equiv.Perm (Fin 22))) := by
    rw [show Subgroup.closure
      ({CFSG.Sporadic.Mathieu.m22gA, CFSG.Sporadic.Mathieu.m22gB} :
        Set (Equiv.Perm (Fin 22))) = H0 from rfl]
    exact hx
  induction hx' using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact u_conj_a_mem
    · exact u_conj_b_mem
  | one => simpa using H0.one_mem
  | mul a b ha hb iha ihb =>
    have h : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
    rw [h]
    exact H0.mul_mem (iha ha) (ihb hb)
  | inv a ha iha =>
    have h : u * a⁻¹ * u⁻¹ = (u * a * u⁻¹)⁻¹ := by group
    rw [h]
    exact H0.inv_mem (iha ha)

theorem a_mem_H0 : S3 0 ∈ H0 := by
  rw [← closure_range_S2]
  exact Subgroup.subset_closure ⟨0, rfl⟩

theorem b_mem_H0 : S3 1 ∈ H0 := by
  rw [← closure_range_S2]
  exact Subgroup.subset_closure ⟨1, rfl⟩

theorem u_mem_normalizer : u ∈ Subgroup.normalizer (H0 : Set (Equiv.Perm (Fin 22))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact u_conj_mem hx
  · intro hx
    have h2 : u⁻¹ = u := inv_eq_of_mul_eq_one_right uU_sq
    have heq : u * (u * x * u⁻¹) * u⁻¹ = x := by
      calc u * (u * x * u⁻¹) * u⁻¹ = (u * u) * x * (u⁻¹ * u⁻¹) := by group
        _ = x := by rw [h2, uU_sq]; group
    rw [← heq]
    exact u_conj_mem hx

theorem N0_le_normalizer : N0 ≤ Subgroup.normalizer (H0 : Set (Equiv.Perm (Fin 22))) := by
  rw [show N0 = Subgroup.closure (Set.range S3) from rfl]
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i
  · exact Subgroup.le_normalizer a_mem_H0
  · exact Subgroup.le_normalizer b_mem_H0
  · exact u_mem_normalizer

theorem sign_u : Equiv.Perm.sign u = -1 := by
  simp [u, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

theorem sign_S2_0 : Equiv.Perm.sign (S2 0) = 1 := by
  simp [S2, List.formPerm, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

theorem sign_S2_1 : Equiv.Perm.sign (S2 1) = 1 := by
  simp [S2, List.formPerm, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

theorem H0_le_alternating : H0 ≤ alternatingGroup (Fin 22) := by
  rw [← closure_range_S2, Subgroup.closure_le]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  change S2 i ∈ alternatingGroup (Fin 22)
  rw [Equiv.Perm.mem_alternatingGroup]
  fin_cases i
  · exact sign_S2_0
  · exact sign_S2_1

theorem u_not_mem_H0 : u ∉ H0 := by
  intro hu
  have h1 : Equiv.Perm.sign u = 1 := by
    have hmem : u ∈ alternatingGroup (Fin 22) := H0_le_alternating hu
    exact Equiv.Perm.mem_alternatingGroup.mp (by exact hmem)
  rw [sign_u] at h1
  exact absurd h1 (by decide)

end CFSG.Sporadic.Mathieu.Asc1113M22

end
