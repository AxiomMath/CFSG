module

public import Certificates.Data.M23Norm3
import Certificates.Kernel.M23Norm3.Glue

public section

namespace Certificates

open CertificateChecks.KernelM23Norm3 in
open Equiv CFSG.M23Norm3 CFSG.M23Heptad CFSG.A7Fano CFSG.QuasithinUnique.Vol2Native.L239 in
open CFSG.ComponentClassification.WittDesign in
theorem certificate7103 :
    m22Count (fun x => badBorel x = true) = 0 ∧
    (∀ σ : Perm (Fin 7), Perm.sign σ = 1 → σ ^ 4 = 1 → σ 4 = 4 → σ 5 = 5 → σ 6 = 6 →
      σ ∈ k4List) ∧
    (∀ σ : Perm (Fin 7), Perm.sign σ = 1 → σ * c33 = c33 * σ →
      ∃ a b : Fin 3, σ = c33 ^ (a : ℕ) * c123 ^ (b : ℕ)) ∧
    (∀ i : Fin 16, ∀ a b : Fin 3,
      M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) * yBar =
        yBar * (M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ)) →
      M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) * uBar =
        uBar * (M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ)) →
      b = 0 ∧ M23Insp.es.getD i 1 * yBar = yBar * M23Insp.es.getD i 1) ∧
    ((∀ i : Fin 7, ((yBar : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) =
        ιbar (c33 i)) ∧
      (∀ i : Fin 7, ((y1Bar : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) =
        ιbar (c123 i)) ∧
      yBar ^ 3 = 1 ∧ yBar ≠ 1 ∧ y1Bar ^ 3 = 1 ∧ uBar * yBar = yBar * uBar ∧ uBar ≠ 1 ∧
      rBar * uBar = uBar * rBar ∧ rBar * yBar * rBar⁻¹ = yBar⁻¹ ∧
      (M23Insp.es.filter (fun e => e * yBar = yBar * e)).length = 4) ∧
    ((∀ x ∈ k4List, ∀ y ∈ k4List, x * y ∈ k4List) ∧ (∀ x ∈ k4List, x⁻¹ ∈ k4List) ∧
      k4List.Nodup ∧ (∀ x ∈ k4List, c123 * x * c123⁻¹ ∈ k4List) ∧
      (∀ x ∈ k4List, c456 * x * c456⁻¹ ∈ k4List) ∧
      (∀ x ∈ k4List, s1245 * x * s1245⁻¹ ∈ k4List) ∧ c123 * c456 = c456 * c123 ∧
      c123 ^ 3 = 1 ∧ c456 ^ 3 = 1 ∧ Perm.sign c123 = 1 ∧ Perm.sign c456 = 1 ∧
      Perm.sign s1245 = 1 ∧ s1245 * c123 * s1245⁻¹ = c123⁻¹ ∧
      s1245 * c456 * s1245⁻¹ = c456⁻¹ ∧ e9List.Nodup) :=
  ⟨m22Count_badBorel, mem_k4, cent, coset_check, yBar_check, perm7_mul, perm7_inv, perm7_nodup,
    perm7_c123, perm7_c456, perm7_s1245, perm7_comm, perm7_c123_pow, perm7_c456_pow,
    perm7_sign_c123, perm7_sign_c456, perm7_sign_s1245, perm7_s_c123, perm7_s_c456, perm7_e9⟩

end Certificates
