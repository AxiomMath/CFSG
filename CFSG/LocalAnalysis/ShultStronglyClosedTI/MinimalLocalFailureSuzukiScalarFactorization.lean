module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem point_eq_mul_of_frattini {H C X : Subgroup G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {ℓ : ℕ} [Fact ℓ.Prime] (hℓX : ℓ ∣ Nat.card X)
    (hℓB : ¬ ℓ ∣ (pairPointStabilizer H beta).relIndex H)
    (hXB : X ≤ pairPointStabilizer H beta)
    (hBX : pairPointStabilizer H beta ≤ Subgroup.normalizer (X : Set G)) (hCH : C ≤ H)
    (hXC : X ≤ Subgroup.normalizer (C : Set G))
    (hHF : ∀ h ∈ H, ∀ c ∈ C ⊔ X, h * c * h⁻¹ ∈ C ⊔ X)
    (hfix : ∀ x ∈ X, x ≠ 1 →
      {ω : rightCosetSpace H | rightCosetTranslate H ω x = ω} = {rightCosetMk H 1, beta}) :
    (C : Set G) * (pairPointStabilizer H beta : Set G) = (H : Set G) := by
  set B := pairPointStabilizer H beta with hBdef
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  have hXH : X ≤ H := hXB.trans hBH
  have hFH : C ⊔ X ≤ H := sup_le hCH hXH
  have hHFn : H ≤ Subgroup.normalizer ((C ⊔ X : Subgroup G) : Set G) := fun h hh =>
    Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hHF h hh y hy, fun hy => by
      have := hHF h⁻¹ (H.inv_mem hh) _ hy
      rwa [show h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y by group] at this⟩
  obtain ⟨S, hS⟩ := exists_isSylowOf ℓ B
  have hSH : IsSylowOf ℓ S H := by
    obtain ⟨hSB, hS2, hSidx⟩ := isSylowOf_iff.mp hS
    refine isSylowOf_iff.mpr ⟨hSB.trans hBH, hS2, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex S B H hSB hBH, Nat.Prime.dvd_mul Fact.out]
    rintro (h1 | h1)
    · exact hSidx h1
    · exact hℓB h1
  have hM := hSH.inf_of_le_normalizer hFH hHFn
  have hSX := hS.inf_of_le_normalizer hXB hBX
  obtain ⟨x, hxSX, hx1⟩ : ∃ x ∈ S ⊓ X, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : S ⊓ X = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    have hcard := hSX.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hv : 0 < (Nat.card X).factorization ℓ :=
      Nat.Prime.factorization_pos_of_dvd Fact.out Nat.card_pos.ne' hℓX
    have : 1 < ℓ ^ (Nat.card X).factorization ℓ :=
      Nat.one_lt_pow hv.ne' (Nat.Prime.one_lt Fact.out)
    omega
  have hNB : H ⊓ Subgroup.normalizer ((S ⊓ (C ⊔ X) : Subgroup G) : Set G) ≤ B := by
    rintro n ⟨hnH, hnN⟩
    have hxM : x ∈ S ⊓ (C ⊔ X) := ⟨hxSX.1, Subgroup.mem_sup_right hxSX.2⟩
    have hnx : n * x * n⁻¹ ∈ S ⊓ (C ⊔ X) := (Subgroup.mem_normalizer_iff.mp hnN x).mp hxM
    have hnxB : n * x * n⁻¹ ∈ B := hS.le hnx.1
    have hω : rightCosetTranslate H (rightCosetTranslate H beta n) x =
        rightCosetTranslate H beta n := by
      have h1 : rightCosetTranslate H beta (n * x * n⁻¹) = beta :=
        (mem_rightCosetStabilizer_iff H beta _).mp hnxB.2
      calc rightCosetTranslate H (rightCosetTranslate H beta n) x
          = rightCosetTranslate H (rightCosetTranslate H beta (n * x * n⁻¹)) n := by
            rw [rightCosetTranslate_mul, rightCosetTranslate_mul]
            congr 1
            group
        _ = rightCosetTranslate H beta n := by rw [h1]
    have hmem : rightCosetTranslate H beta n ∈
        {ω : rightCosetSpace H | rightCosetTranslate H ω x = ω} := hω
    rw [hfix x hxSX.2 hx1] at hmem
    have hnα : rightCosetTranslate H (rightCosetMk H 1) n = rightCosetMk H 1 :=
      (PairInvolutionFixedField.translate_base_iff H n).mpr hnH
    rcases hmem with h2 | h2
    · exfalso
      apply hbeta
      have h3 := congrArg (fun ω => rightCosetTranslate H ω n⁻¹) (h2.trans hnα.symm)
      simpa only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] using h3
    · exact ⟨(mem_rightCosetStabilizer_iff H _ n).mpr hnα,
        (mem_rightCosetStabilizer_iff H _ n).mpr h2⟩
  obtain ⟨S', hS'⟩ := hM
  apply Set.Subset.antisymm
  · rintro _ ⟨c, hc, b, hb, rfl⟩
    exact H.mul_mem (hCH hc) (hBH hb)
  · intro h hh
    obtain ⟨c, hc, hch⟩ := exists_mul_mem_normalizer_of_sylow hHF S' hS' hh
    have hchB : c * h ∈ B := hNB ⟨H.mul_mem (hFH hc) hh, hch⟩
    have hc' : c⁻¹ ∈ ((C ⊔ X : Subgroup G) : Set G) := (C ⊔ X).inv_mem hc
    rw [Subgroup.coe_mul_of_right_le_normalizer_left C X hXC] at hc'
    obtain ⟨c₁, hc₁, x₁, hx₁, hcx⟩ := hc'
    refine ⟨c₁, hc₁, x₁ * (c * h), B.mul_mem (hXB hx₁) hchB, ?_⟩
    have hcx' : c₁ * x₁ = c⁻¹ := hcx
    show c₁ * (x₁ * (c * h)) = h
    rw [← mul_assoc, hcx', inv_mul_cancel_left]

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
