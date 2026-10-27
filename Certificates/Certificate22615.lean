module

public import Certificates.Kernel.SporSch.HeT.C22615
public import Certificates.Kernel.SporSch.HeT.Facts2115
public import Certificates.Kernel.SporSch.HeT.Facts2118
public import CFSG.Certificates.Kernel.SporSch.SporXElemSound

public section

namespace CertificateChecks.Batch22615

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporXE CFSG.KS.SporSch CFSG.KD.He8330.C22615 CFSG.Sporadic.HeldB
open CFSG.Sporadic.Schreier CertificateChecks.KernelSpor CertificateChecks.KernelSporSch.HeCn
open Subgroup

theorem baseF : BaseFaithful heP bsP := fun h hh hfix =>
  eq_one_of_fix_base hh fun b hb => hfix b (by
    simp only [bsP, List.mem_cons, List.not_mem_nil, or_false]
    omega)

theorem bs_lt : ∀ b ∈ bsP, b < 8330 := by decide

theorem repS {k : Nat} (hk : k < 2) : RepF 8330 (pm (HeC.S k)) (heGenPerm k) := by
  have h := rep_heGen hk
  rw [CertificateChecks.KernelSporSch.HeO16.gen_eq k hk] at h
  exact repF_of_rep h

theorem repT1 : RepF 8330 (pm T1) heT1P := by
  have h := CertificateChecks.KernelSporSch.HeF15.rep_heT1'
  rw [CertificateChecks.KernelSporSch.HeF15.T1_eq.1] at h
  exact repF_of_rep h

@[expose] noncomputable def gU (l : Nat) : Equiv.Perm (Fin 8330) :=
  [heGenPerm 0, heGenPerm 1, heAutU * heGenPerm 0 * heAutU, heAutU * heGenPerm 1 * heAutU].getD l 1

theorem lU_two : lU 2 = fun x => pm U5 (pm (HeC.S 0) (pm U5 x)) := rfl

theorem lU_three : lU 3 = fun x => pm U5 (pm (HeC.S 1) (pm U5 x)) := rfl

theorem repU' : ∀ l < 4, RepF 8330 (lU l) (gU l) := by
  intro l hl
  interval_cases l <;> simp only [gU, List.getD_cons_zero, List.getD_cons_succ]
  · exact repS (by norm_num)
  · exact repS (by norm_num)
  · rw [lU_two]
    exact (CertificateChecks.KernelSporSch.HeF18.repU.comp (repS (k := 0)
      (by norm_num))).comp CertificateChecks.KernelSporSch.HeF18.repU
  · rw [lU_three]
    exact (CertificateChecks.KernelSporSch.HeF18.repU.comp (repS (k := 1)
      (by norm_num))).comp CertificateChecks.KernelSporSch.HeF18.repU

theorem gU_mem : ∀ l < 4, gU l ∈ heP := by
  intro l hl
  interval_cases l <;> simp only [gU, List.getD_cons_zero, List.getD_cons_succ]
  · exact heGenPerm_mem (by norm_num)
  · exact heGenPerm_mem (by norm_num)
  · exact heAutU_conj_mem (heGenPerm_mem (by norm_num))
  · exact heAutU_conj_mem (heGenPerm_mem (by norm_num))

theorem elemP {L : Nat → Nat → Nat} {g : Nat → Equiv.Perm (Fin 8330)} {nl : Nat}
    (hL : ∀ l < nl, RepF 8330 (L l) (g l)) (hg : ∀ l < nl, g l ∈ heP) {t : Nat → Nat}
    {τ : Equiv.Perm (Fin 8330)} (ht : RepF 8330 t τ)
    (hτ : ∀ x ∈ heP, (x * τ)⁻¹ * (τ * x) ∈ heP) {words : List (List Nat × Nat)}
    (hck : ckE bsP L nl words = true) (hcm : cmB bsP t (words.map (eF L)) = true) :
    ∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {τ} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
      2 ^ words.length ≤ Nat.card E := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (distB bsP (sF (words.map (eF L))))
        (csB bsP (words.map (eF L)))) (ltW nl words) = true := hck
  rw [bAnd_iff, ltW_iff] at h'
  have hlt := h'.1
  have hx : ∀ we ∈ words, (we.1.map g).prod ^ we.2 ∈ heP := fun we hwe => by
    refine pow_mem (list_prod_mem fun y hy => ?_) _
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
    exact hg l (hlt we hwe l hl)
  exact elem_of_ckE_le baseF bs_lt le_rfl hL hg
    (cent_of_cmB baseF hL ht hlt (fun we hwe => hτ _ (hx we hwe)) hcm) hck

theorem inP {τ : Equiv.Perm (Fin 8330)} (h : τ ∈ heP) :
    ∀ x ∈ heP, (x * τ)⁻¹ * (τ * x) ∈ heP := fun _ hx =>
  heP.mul_mem (heP.inv_mem (heP.mul_mem hx h)) (heP.mul_mem h hx)

theorem elem_all :
    (∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {heGenPerm 0} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ 4 ≤ Nat.card E) ∧
    (∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {heT1P} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ 4 ≤ Nat.card E) ∧
    (∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {heAutU} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ 3 ≤ Nat.card E) := by
  have hA : ∀ l < 2, RepF 8330 (lA l) (heGenPerm l) := fun l hl => repS hl
  have hAm : ∀ l < 2, heGenPerm l ∈ heP := fun l hl => heGenPerm_mem hl
  refine ⟨?_, ?_, ?_⟩
  · have h := elemP hA hAm (repS (k := 0) (by norm_num)) (inP (heGenPerm_mem (by norm_num))) ck0
      cm0
    have hl : w0.length = 4 := rfl
    rwa [hl] at h
  · have h := elemP hA hAm repT1 (inP heT1P_mem) ck1 cm1
    have hl : w1.length = 4 := rfl
    rwa [hl] at h
  · have h := elemP repU' gU_mem CertificateChecks.KernelSporSch.HeF18.repU
      (fun _ hx => heAutU_comm_mem hx) ckU cmU
    have hl : wU.length = 3 := rfl
    rwa [hl] at h

end CertificateChecks.Batch22615

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HeldB Subgroup in
theorem certificate22615 :
    (∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {heGenPerm 0} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ 4 ≤ Nat.card E) ∧
    (∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {heT1P} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ 4 ≤ Nat.card E) ∧
    (∃ E : Subgroup (Equiv.Perm (Fin 8330)), E ≤ heP ⊓ centralizer {heAutU} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧ 2 ^ 3 ≤ Nat.card E) := CertificateChecks.Batch22615.elem_all

end Certificates
