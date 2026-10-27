module

public import Certificates.Data.OmegaS107Facts

public section

namespace Certificates.OmegaF1051

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups Certificates.OmegaS107

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

structure Facts : Prop where
  z_sq : z0 * z0 = 1
  z_ne : z0 ≠ 1
  z_mem : z0 ∈ QT0.originalSubgroup
  z_comm : ∀ t ∈ QT0.originalSubgroup, t * z0 = z0 * t
  card_CA : Nat.card ↥(QA45.originalSubgroup ⊓ Subgroup.centralizer ({z0} : Set P45)) = 1152
  card_CP : Nat.card ↥(QP45.originalSubgroup ⊓ Subgroup.centralizer ({z0} : Set P45)) = 576
  card_Q0 : Nat.card Q0 = 32
  mem_q0l : ∀ g : P45, g ∈ q0l () ↔ g ∈ Q0
  nodup_q0l : (q0l ()).Nodup
  le_oTwo : Q0 ≤ Subgroup.closure
    {x : P45 | x ∈ QP45.originalSubgroup ⊓ Subgroup.centralizer ({z0} : Set P45) ∧ Odd (orderOf x)}
  normal : ∀ c ∈ QA45.originalSubgroup ⊓ Subgroup.centralizer ({z0} : Set P45), ∀ q ∈ Q0,
    c * q * c⁻¹ ∈ Q0
  ext : ∀ U : Subgroup P45, U ≤ QA45.originalSubgroup → (∀ u ∈ U, u * z0 = z0 * u) → Q0 ≤ U →
    (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Q0 ∧ a * a ∈ Q0) → ∀ n : ℕ, 1 ≤ n →
      Q0.relIndex U = 2 ^ n → n ≤ 2 ∧
        2 ^ n * Nat.card {q : P45 // q ∈ Q0 ∧ ∀ u ∈ U, q * u * q⁻¹ * u⁻¹ ∈ Subgroup.zpowers z0} < 32

end Certificates.OmegaF1051

end
