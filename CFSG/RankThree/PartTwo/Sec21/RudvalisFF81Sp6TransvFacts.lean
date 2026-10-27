module

public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import Certificates.Data.RudvalisFF81Sp6Transv

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

@[expose] def qCode : Fin 5 → List ℕ := ![qG0, qG1, qG2, qG3, qG4]

@[expose] def Sp6TransvAt (z : Fin 3 → H6) (t s f0 f2 : H6) (Q : Subgroup H6) : Prop :=
  (s * s = 1 ∧ s ≠ 1 ∧ s * z 0 = z 0 * s ∧ s * z 2 = z 2 * s ∧ s * z 1 * s⁻¹ = (z 1)⁻¹ ∧
    f0 * f0 = 1 ∧ f0 * z 0 * f0⁻¹ = (z 0)⁻¹ ∧ f0 * z 1 = z 1 * f0 ∧ f0 * z 2 = z 2 * f0 ∧
    f2 * f2 = 1 ∧ f2 * z 2 * f2⁻¹ = (z 2)⁻¹ ∧ f2 * z 0 = z 0 * f2 ∧ f2 * z 1 = z 1 * f2) ∧
  Nat.card (Subgroup.centralizer ({s} : Set H6)) = 23040 ∧
  (∀ R : Subgroup H6, R ≤ Subgroup.centralizer ({s} : Set H6) → IsPGroup 2 R →
    Subgroup.centralizer ({s} : Set H6) ≤ Subgroup.normalizer (R : Set H6) →
      R ≤ Subgroup.zpowers s ∨ R = Q) ∧
  Q ≤ Subgroup.centralizer ({s} : Set H6) ∧ Nat.card Q = 32 ∧
  (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ (∀ x ∈ Q, x * x = 1) ∧
  Nat.card ↥(Q ⊓ Subgroup.centralizer ({z 0} : Set H6)) = 8 ∧
  Nat.card ↥(Q ⊓ Subgroup.centralizer ({z 2} : Set H6)) = 8 ∧
  Nat.card ↥(Q ⊓ Subgroup.centralizer ({z 0} : Set H6) ⊓
    Subgroup.centralizer ({z 2} : Set H6)) = 2 ∧
  Nat.card ↥(Q ⊓ Subgroup.centralizer ({z 0 * z 2} : Set H6)) = 2 ∧
  Nat.card ↥(Q ⊓ Subgroup.centralizer ({z 0 * z 2 ^ 2} : Set H6)) = 2 ∧
  s ∈ ⁅Q, Subgroup.centralizer ({s} : Set H6)⁆ ∧
  (∀ x : H6, x * z 0 = z 0 * x → x * z 2 = z 2 * x → x * x = 1 → x ≠ 1 →
    x * z 1 * x⁻¹ = (z 1)⁻¹ → x = s ∨ x = z 1 * s * (z 1)⁻¹ ∨ x = (z 1)⁻¹ * s * z 1) ∧
  (∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ j < 3,
    (z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j) ^ 3 = 1 → z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j ≠ 1 →
      (∃ g : H6, z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j = g * z 1 * g⁻¹) ∨
      (∃ g : H6, z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j = g * (z 0 * z 1) * g⁻¹) ∨
      (∃ g : H6, z 0 ^ a * z 1 ^ b * z 2 ^ c * t ^ j = g * (z 0 * z 1 * z 2) * g⁻¹)) ∧
  ∀ i, (∃ g : H6, z i = g * z 1 * g⁻¹) ∧ ∃ g : H6, (z i)⁻¹ = g * z 1 * g⁻¹

@[expose] def Sp6TransvFacts : Prop :=
  ((∃ s : H6, mat6 s = dec6 s0C) ∧ (∃ f : H6, mat6 f = dec6 fl0C) ∧
    (∃ f : H6, mat6 f = dec6 fl2C) ∧ ∀ i, ∃ q : H6, mat6 q = dec6 (qCode i)) ∧
  ∀ (z : Fin 3 → H6) (t s f0 f2 : H6) (q : Fin 5 → H6),
    (∀ i, mat6 (z i) = dec6 (zCode i)) → mat6 t = dec6 tCode → mat6 s = dec6 s0C →
    mat6 f0 = dec6 fl0C → mat6 f2 = dec6 fl2C → (∀ i, mat6 (q i) = dec6 (qCode i)) →
    Sp6TransvAt z t s f0 f2 (Subgroup.closure (Set.range q))

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

end
