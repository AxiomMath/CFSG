module

public import Certificates.Data.OmegaPk

public section

namespace Certificates.OmegaPk

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check
  Certificates.P43Twin

local notation "P45" => Equiv.Perm (Fin 45)

abbrev pkP : Subgroup P45 := QP45.originalSubgroup

abbrev pkC : Subgroup P45 := pkP ⊓ Subgroup.centralizer ({tA ()} : Set P45)

abbrev pkCB : Subgroup P45 := pkP ⊓ Subgroup.centralizer ({tB ()} : Set P45)

abbrev pkRho : SL23 → P45 := rhoOf (rhoTab ())

structure Facts : Prop where
  ordA : orderOf (tA ()) = 2
  ordB : orderOf (tB ()) = 2
  cardC : Nat.card pkC = 576
  cardCB : Nat.card pkCB = 96
  cover : ∀ p ∈ pkP, p * p = 1 → p ≠ 1 → ∃ g ∈ pkP, g * p * g⁻¹ = tA () ∨ g * p * g⁻¹ = tB ()
  rho : (∀ A B, pkRho (A * B) = pkRho A * pkRho B) ∧ (∀ A, pkRho A = 1 → A = 1) ∧
    (∀ A, pkRho A ∈ pkP) ∧ (∀ A, pkRho A * tA () = tA () * pkRho A) ∧ ∃ A, pkRho A = tA ()
  subQ1 : (∀ q ∈ Q1 (), q ∈ pkC) ∧ (1 : P45) ∈ Q1 () ∧ (∀ a ∈ Q1 (), ∀ b ∈ Q1 (), a * b ∈ Q1 ()) ∧
    ∀ a ∈ Q1 (), a⁻¹ ∈ Q1 ()
  subQ2 : (∀ q ∈ Q2 (), q ∈ pkC) ∧ (1 : P45) ∈ Q2 () ∧ (∀ a ∈ Q2 (), ∀ b ∈ Q2 (), a * b ∈ Q2 ()) ∧
    ∀ a ∈ Q2 (), a⁻¹ ∈ Q2 ()
  centA : (∀ A, ∀ q ∈ Q2 (), pkRho A * q = q * pkRho A) ∧
    ∀ x ∈ pkP, (∀ q ∈ Q2 (), x * q = q * x) → ∃ A, pkRho A = x
  centB : (∀ A, ∀ q ∈ Q1 (), cj (g0 ()) (pkRho A) * q = q * cj (g0 ()) (pkRho A)) ∧
    ∀ x ∈ pkP, (∀ q ∈ Q1 (), x * q = q * x) → ∃ A, cj (g0 ()) (pkRho A) = x
  memG : g0 () ∈ pkC
  comm : (∀ A B, pkRho A * cj (g0 ()) (pkRho B) = cj (g0 ()) (pkRho B) * pkRho A) ∧
    ∃ A, ∀ B, pkRho A ≠ cj (g0 ()) (pkRho B)
  nsQ1 : ∀ x ∈ pkC, x ^ 3 = 1 → ¬ (∀ q ∈ Q1 (), x * q = q * x) →
    ∀ q ∈ Q1 (), ∃ q' ∈ Q1 (), q = x * q' * x⁻¹ * q'⁻¹ ∨ q = tA () * (x * q' * x⁻¹ * q'⁻¹)
  nsQ2 : ∀ x ∈ pkC, x ^ 3 = 1 → ¬ (∀ q ∈ Q2 (), x * q = q * x) →
    ∀ q ∈ Q2 (), ∃ q' ∈ Q2 (), q = x * q' * x⁻¹ * q'⁻¹ ∨ q = tA () * (x * q' * x⁻¹ * q'⁻¹)
  prod : ∃ s : Finset P45, s.card = 32 ∧ ∀ p ∈ s, ∃ q ∈ Q1 (), ∃ r ∈ Q2 (), p = q * r
  e : (∀ x ∈ pkC, x ^ 9 = 1 → ∃ A B, pkRho A * cj (g0 ()) (pkRho B) = x) ∧
    (∀ x ∈ pkC, (¬ ∃ A B, pkRho A * cj (g0 ()) (pkRho B) = x) →
      (∀ A, ∃ B, cj (g0 ()) (pkRho B) = x⁻¹ * pkRho A * x) ∧
        ∀ B, ∃ A, pkRho A = x⁻¹ * cj (g0 ()) (pkRho B) * x) ∧
    ∀ b ∈ pkC, ((∃ A B, pkRho A * cj (g0 ()) (pkRho B) = b) ↔
      ¬ ∃ A B, pkRho A * cj (g0 ()) (pkRho B) = b * g0 ())
  noOddA : (∀ o ∈ pkC, o ≠ 1 → o ^ 3 = 1 → ∃ c ∈ pkC, (o * (c * o * c⁻¹)) ^ 3 ≠ 1) ∧
    ∀ x ∈ pkC, x ^ 9 = 1 → x ^ 3 = 1
  noOddB : (∀ o ∈ pkCB, o ≠ 1 → o ^ 3 = 1 → ∃ c ∈ pkCB, (o * (c * o * c⁻¹)) ^ 3 ≠ 1) ∧
    ∀ x ∈ pkCB, x ^ 9 = 1 → x ^ 3 = 1
  u : ∃ U : List P45, U.length = 12 ∧ (1 : P45) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧
    (∀ a ∈ U, a⁻¹ ∈ U) ∧ ∀ x ∈ pkCB, x ^ 3 = 1 → x ∈ U
  pair : ∀ a ∈ pkC, ∀ b ∈ pkC, a * a = tA () → b * b = tA () → b * a = tA () * a * b →
    (∀ q ∈ Q1 (), q ∈ q8B (tA ()) a b) ∨ ∀ q ∈ Q2 (), q ∈ q8B (tA ()) a b

end Certificates.OmegaPk
