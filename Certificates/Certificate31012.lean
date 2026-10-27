module

public import CFSG.Sporadic.Schreier.TitsCert
import Certificates.Kernel.CentGenK.Glue
import Certificates.Kernel.CentGenK.Tits
import Certificates.Kernel.Sporadic.Tits.Words2264

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.CentGenK CFSG.KS.Raw.Orb CFSG.Sporadic.Schreier.Tits
  CertificateChecks.KernelSpor.Tits2264 in
open CFSG.Sporadic.Schreier.Tits in
open scoped commutatorElement in
theorem certificate31012 : ∃ x y s₁ s₂ : Equiv.Perm (Fin 1755),
    Subgroup.closure {s₁, s₂} = titsD ∧ x ∈ titsD ∧ y ∈ titsD ∧
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      (∀ k < 3, ⁅x, y⁆ ≠ x ^ k) ∧ (∀ k < 3, ⁅x, y⁆ ≠ y ^ k) ∧
      s₁ * x = x * s₁ ∧ s₂ * y = y * s₂ := by
  have hk : ∀ j < 2, PRep 1755 11 (CertificateChecks.KernelSpor.TitsD.S j) (titsDGen j) :=
    fun j hj => prep_of_rep (by
      rw [← Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec dOK j hj), ← titsDArr_eq hj]
      exact titsDArr_rep hj)
  have hD : titsD = Subgroup.closure {titsDGen 0, titsDGen 1} := by
    unfold titsD
    congr 1
    ext g
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      Fin.val_zero, Fin.val_one]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  rw [hD]
  exact hp_facts (hk 0 (by norm_num)) (hk 1 (by norm_num)) KernelCentGenK.Tits.tits_ok

end Certificates
