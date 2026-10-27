module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import Certificates.Data.RudvalisFF81Sp6ShortRoot

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR

open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

@[expose] def SRConcl {X : Type} [Group X] (L : Subgroup X) (b₁ b₂ b₃ s : X) : Prop :=
  (∃ v ∈ L ⊓ Cen s ⊓ Cen (b₁ * (b₂ * b₃)), v ^ 4 = 1 ∧ v ≠ 1 ∧ v ≠ s) ∧
  (∃ v ∈ L ⊓ Cen s ⊓ Cen b₁, v * v = 1 ∧
    (∀ g ∈ L ⊓ Cen s ⊓ Cen b₁, g * v * g⁻¹ * v = v * (g * v * g⁻¹)) ∧ v ≠ 1 ∧ v ≠ s) ∧
  ∀ R : Subgroup X, R ≤ L ⊓ Cen s → IsPGroup 2 R → L ⊓ Cen s ≤ Nor R → s ∈ R →
    (Nat.card R = 2 ∧ Nat.card ↥(R ⊓ Cen b₁) = 2 ∧ Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃))) = 2 ∧
      Nat.card ↥(R ⊓ Cen (b₂ * b₃)) = 2) ∨
    (Nat.card R = 8 ∧ Nat.card ↥(R ⊓ Cen b₁) = 8 ∧ Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃))) = 2 ∧
      Nat.card ↥(R ⊓ Cen (b₂ * b₃)) = 2 ∧
      ∀ v ∈ L ⊓ Cen s ⊓ Cen (b₁ * (b₂ * b₃)), v ^ 4 = 1 → v ∈ CenS R) ∨
    (Nat.card R = 32 ∧ Nat.card ↥(R ⊓ Cen b₁) = 2 ∧ Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃))) = 8 ∧
      Nat.card ↥(R ⊓ Cen (b₂ * b₃)) = 2 ∧
      ∀ v ∈ L ⊓ Cen s ⊓ Cen b₁, v * v = 1 →
        (∀ g ∈ L ⊓ Cen s ⊓ Cen b₁, g * v * g⁻¹ * v = v * (g * v * g⁻¹)) → v ∈ CenS R) ∨
    (Nat.card R = 128 ∧ Nat.card ↥(R ⊓ Cen b₁) = 8 ∧
      Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃))) = 8 ∧ Nat.card ↥(R ⊓ Cen (b₂ * b₃)) = 2 ∧
      IsElemAb 2 3 (R ⊓ Cen b₁) ∧ R ⊓ Cen (b₁ * (b₂ * b₃)) ≤ CenS (R ⊓ Cen b₁) ∧
      R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)) ≤ CenS (R ⊓ Cen b₁) ∧
      R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)) ≤ CenS (R ⊓ Cen (b₁ * (b₂ * b₃))) ∧
      Nat.card ↥(R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃))) = 32 ∧
      (∀ q ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)),
        (∀ y ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)), q * y = y * q) →
          q = 1 ∨ q = s) ∧
      (∀ q ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)), q * q = 1 ∨ q * q = s) ∧
      (∀ q ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)),
        ∀ y ∈ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)),
          q * y * q⁻¹ * y⁻¹ = 1 ∨ q * y * q⁻¹ * y⁻¹ = s) ∧
      ∃ A : Subgroup X, A ≤ R ⊓ Cen (b₁ * (b₂ * b₃)) ⊔ R ⊓ Cen (b₁⁻¹ * (b₂ * b₃)) ∧
        IsElemAb 2 3 A ∧ s ∈ A)

@[expose] def Sp6SRAt (z : Fin 3 → H6) (s : H6) : Prop :=
  (s * s = 1 ∧ s ≠ 1 ∧ s * z 0 = z 0 * s ∧ s * (z 1 * z 2) = z 1 * z 2 * s ∧
    s * (z 1 * z 2 ^ 2) * s⁻¹ = (z 1 * z 2 ^ 2)⁻¹) ∧
  Nat.card (Cen s) = 4608 ∧
  SRConcl ⊤ (z 0) (z 1) (z 2) s ∧
  (∀ R : Subgroup H6, R ≤ Cen s → IsPGroup 2 R → Cen s ≤ Nor R → Nat.card R ≤ 128) ∧
  ∀ x : H6, x * z 0 = z 0 * x → x * (z 1 * z 2) = z 1 * z 2 * x → x * x = 1 → x ≠ 1 →
    x * (z 1 * z 2 ^ 2) * x⁻¹ = (z 1 * z 2 ^ 2)⁻¹ →
      x = s ∨ x = z 1 * z 2 ^ 2 * s * (z 1 * z 2 ^ 2)⁻¹ ∨ x = (z 1 * z 2 ^ 2)⁻¹ * s * (z 1 * z 2 ^ 2)

@[expose] def Sp6SRFacts : Prop :=
  (∃ s : H6, mat6 s = dec6 srC) ∧
  ∀ (z : Fin 3 → H6) (s : H6), (∀ i, mat6 (z i) = dec6 (zCode i)) → mat6 s = dec6 srC →
    Sp6SRAt z s

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6SR

end
