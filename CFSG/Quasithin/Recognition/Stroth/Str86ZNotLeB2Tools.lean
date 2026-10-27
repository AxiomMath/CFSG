module

public import Mathlib.GroupTheory.Commutator.Basic

import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.Stroth

open scoped commutatorElement

variable {G : Type} [Group G]

theorem sup_inf_eq_sup_inf_of_le_normalizer {D Q R : Subgroup G} (hDR : D ≤ R)
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) : (D ⊔ Q) ⊓ R = D ⊔ (Q ⊓ R) := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (le_inf le_sup_left hDR) (inf_le_inf_right R le_sup_right))
  obtain ⟨hxDQ, hxR⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨d, hd, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hDQ).mp hxDQ
  have hqR : q ∈ R := by
    have h := R.mul_mem (R.inv_mem (hDR hd)) hxR
    rwa [inv_mul_cancel_left] at h
  exact Subgroup.mul_mem_sup hd (Subgroup.mem_inf.mpr ⟨hq, hqR⟩)

theorem commutator_sup_le_sup_of_le_normalizer {D Q : Subgroup G}
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) : ⁅D ⊔ Q, D ⊔ Q⁆ ≤ ⁅D, D⁆ ⊔ Q := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hyN : y ∈ Subgroup.normalizer (Q : Set G) := sup_le hDQ Subgroup.le_normalizer hy
  obtain ⟨d₁, hd₁, q₁, hq₁, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hDQ).mp hx
  obtain ⟨d₂, hd₂, q₂, hq₂, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hDQ).mp hy
  have e : ⁅d₁ * q₁, d₂ * q₂⁆ =
      (d₁ * (q₁ * ((d₂ * q₂) * q₁⁻¹ * (d₂ * q₂)⁻¹)) * d₁⁻¹) * ⁅d₁, d₂⁆ *
        (d₂ * (d₁ * q₂ * d₁⁻¹ * q₂⁻¹) * d₂⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have h₁ : (d₂ * q₂) * q₁⁻¹ * (d₂ * q₂)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hyN _).mp (Q.inv_mem hq₁)
  have hA : d₁ * (q₁ * ((d₂ * q₂) * q₁⁻¹ * (d₂ * q₂)⁻¹)) * d₁⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hDQ hd₁) _).mp (Q.mul_mem hq₁ h₁)
  have h₂ : d₁ * q₂ * d₁⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hDQ hd₁) _).mp hq₂
  have hC : d₂ * (d₁ * q₂ * d₁⁻¹ * q₂⁻¹) * d₂⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hDQ hd₂) _).mp (Q.mul_mem h₂ (Q.inv_mem hq₂))
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hA)
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hd₁ hd₂)))
    (Subgroup.mem_sup_right hC)

theorem commutator_sup_le_of_commutator_le {D Q : Subgroup G}
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hD : ⁅D, D⁆ ≤ Q) : ⁅D ⊔ Q, D ⊔ Q⁆ ≤ Q :=
  (commutator_sup_le_sup_of_le_normalizer hDQ).trans (sup_le hD le_rfl)

theorem commutatorElement_mul_mul_mul_inv_mem {X Z K : Subgroup G} (hZX : Z ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hZ : ∀ z ∈ Z, ∀ x ∈ X, ⁅z, x⁆ ∈ K)
    {x y e₁ e₂ : G} (hx : x ∈ X) (hy : y ∈ X) (he₁ : e₁ ∈ Z) (he₂ : e₂ ∈ Z) :
    ⁅x * e₁, y * e₂⁆ * ⁅x, y⁆⁻¹ ∈ K := by
  have e : ⁅x * e₁, y * e₂⁆ * ⁅x, y⁆⁻¹ =
      (x * ⁅e₁, y * e₂⁆ * x⁻¹) * (⁅x, y⁆ * (y * ⁅e₂, x⁆⁻¹ * y⁻¹) * ⁅x, y⁆⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  have hxy : ⁅x, y⁆ ∈ X := by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)
  have h₁ : x * ⁅e₁, y * e₂⁆ * x⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hXK hx) _).mp (hZ e₁ he₁ _ (X.mul_mem hy (hZX he₂)))
  have h₂ : y * ⁅e₂, x⁆⁻¹ * y⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hXK hy) _).mp (K.inv_mem (hZ e₂ he₂ x hx))
  exact K.mul_mem h₁ ((Subgroup.mem_normalizer_iff.mp (hXK hxy) _).mp h₂)

theorem commutator_le_of_le_sup_of_inf_le {N A B C K : Subgroup G} (hA : A ≤ N) (hB : B ≤ N)
    (hC : C ≤ N) (hNA : N ≤ Subgroup.normalizer (A : Set G))
    (hNB : N ≤ Subgroup.normalizer (B : Set G)) (hNC : N ≤ Subgroup.normalizer (C : Set G))
    (hNK : N ≤ Subgroup.normalizer (K : Set G)) (hAB : A ⊓ B ≤ K) (hAC : A ⊓ C ≤ K)
    (hABC : A ≤ B ⊔ C) : ⁅A, A⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha a' ha'
  obtain ⟨b, hb, c, hc, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer (hB.trans hNC)).mp (hABC ha')
  have hmem : ∀ X : Subgroup G, X ≤ N → N ≤ Subgroup.normalizer (X : Set G) →
      ∀ x ∈ X, ⁅a, x⁆ ∈ A ⊓ X := by
    intro X hX hNX x hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (hNA (hX hx)) a⁻¹).mp (A.inv_mem ha)
      have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact A.mul_mem ha h
    · have h := (Subgroup.mem_normalizer_iff.mp (hNX (hA ha)) x).mp hx
      rw [commutatorElement_def]
      exact X.mul_mem h (X.inv_mem hx)
  have h₁ := hAB (hmem B hB hNB b hb)
  have h₂ := hAC (hmem C hC hNC c hc)
  have e : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact K.mul_mem h₁ ((Subgroup.mem_normalizer_iff.mp (hNK (hB hb)) _).mp h₂)

end CFSG.Quasithin.Stroth

end
