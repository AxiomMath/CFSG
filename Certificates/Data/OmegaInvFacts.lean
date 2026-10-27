module

public import Certificates.Data.OmegaInv

public section

namespace Certificates.OmegaInv

open CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

structure Facts : Prop where
  rep : ∀ r ∈ reps (), r ∈ QA45.originalSubgroup ∧ r * r = 1 ∧ r ≠ 1
  z0_mem : Certificates.OmegaT0.z0 () ∈ QP45.originalSubgroup
  yB_mem : Certificates.OmegaT0.yB () ∈ QP45.originalSubgroup
  r3_not : r3 () ∉ QP45.originalSubgroup
  r4_not : r4 () ∉ QP45.originalSubgroup
  cent : Nat.card ↥(QA45.originalSubgroup ⊓
        Subgroup.centralizer ({Certificates.OmegaT0.z0 ()} : Set P45)) = 1152 ∧
      Nat.card ↥(QA45.originalSubgroup ⊓
        Subgroup.centralizer ({Certificates.OmegaT0.yB ()} : Set P45)) = 192 ∧
      Nat.card ↥(QA45.originalSubgroup ⊓ Subgroup.centralizer ({r3 ()} : Set P45)) = 96 ∧
      Nat.card ↥(QA45.originalSubgroup ⊓ Subgroup.centralizer ({r4 ()} : Set P45)) = 1440
  fix : fixCnt (Certificates.OmegaT0.z0 ()) = 13 ∧ fixCnt (Certificates.OmegaT0.yB ()) = 5 ∧
    fixCnt (r3 ()) = 7 ∧ fixCnt (r4 ()) = 15
  cover : ∀ t ∈ QA45.originalSubgroup, t * t = 1 → t ≠ 1 →
    ∃ g ∈ QP45.originalSubgroup, ∃ r ∈ reps (), g * t * g⁻¹ = r
  s6 : Nonempty (↥(QP45.originalSubgroup ⊓ Subgroup.centralizer ({r4 ()} : Set P45)) ≃*
    Equiv.Perm (Fin 6))

end Certificates.OmegaInv

end
