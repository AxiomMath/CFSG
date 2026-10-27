module

public import CFSG.RankThree.PartTwo.Sec14.Item148RankProofFieldTools

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag

theorem exists_second_field_element {F : Type} [Field F] [Finite F]
    {E : Subgroup (MulAut (projectiveSL 3 F))} (hE : CFSG.Open.IsElemAbelian 3 E)
    {H : GL (Fin 3) F} {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (hφE : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ ∈ E)
    (hφN : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ ∉ linearAutGroup 3 F)
    {y : MulAut (projectiveSL 3 F)} (hyE : y ∈ E) (hyN : y ∈ linearAutGroup 3 F) :
    ∃ (σ' : F ≃+* F) (H' : GL (Fin 3) F), orderOf σ' = 3 ∧
      conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ * y =
        conjAut 3 F H' * fieldAut 3 F σ' * (conjAut 3 F H')⁻¹ ∧
      (σ' = σ ∨ σ' * σ = 1) ∧ ∀ x, σ' x = x ↔ σ x = x := by
  have hψE : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ * y ∈ E := E.mul_mem hφE hyE
  have hψN : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ * y ∉ linearAutGroup 3 F := by
    intro hm
    apply hφN
    have hm' := (linearAutGroup 3 F).mul_mem hm ((linearAutGroup 3 F).inv_mem hyN)
    rwa [mul_inv_cancel_right] at hm'
  have hψ3 : (conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ * y) ^ 3 = 1 :=
    hE.2 _ hψE
  obtain ⟨σ', hσ', H', hψH⟩ := linear_order_three_field_descent (le_refl 3) _ hψ3 hψN
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨ℓ, -, e, hℓ, hcard⟩ := FiniteField.card' F
  have hcard' : Nat.card F = ℓ ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hone : 1 ≤ (e : ℕ) := by have := e.pos; omega
  have h12 := CFSG.RankThree.PartTwo.Sec14.Item148Rank.ringAut_eq_or_mul_eq_one148 hℓ hone
    hcard' hσ hσ'
  refine ⟨σ', H', hσ', hψH, h12, ?_⟩
  rcases h12 with h1 | h1
  · intro x
    rw [h1]
  · have h2 : σ' = σ⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hinv : ∀ z, σ⁻¹ (σ z) = z := fun z => by simp
    have hinv' : ∀ z, σ (σ⁻¹ z) = z := fun z => by simp
    intro x
    rw [h2]
    constructor
    · intro hx
      calc σ x = σ (σ⁻¹ x) := by rw [hx]
        _ = x := hinv' x
    · intro hx
      calc σ⁻¹ x = σ⁻¹ (σ x) := by rw [hx]
        _ = x := hinv x

theorem exists_second_field_element_psu {p f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData p f K} (hq : 2 < p ^ f)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : CFSG.Open.IsElemAbelian 3 E)
    {H : unitaryIsom3 h} {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (hφE : psuConj h H * psuField h σ * (psuConj h H)⁻¹ ∈ E)
    (hφN : psuConj h H * psuField h σ * (psuConj h H)⁻¹ ∉ (psuConj h).range)
    {y : MulAut (unitaryPSU h 3)} (hyE : y ∈ E) (hyN : y ∈ (psuConj h).range) :
    ∃ (σ' : K ≃+* K) (H' : unitaryIsom3 h), orderOf σ' = 3 ∧
      psuConj h H * psuField h σ * (psuConj h H)⁻¹ * y =
        psuConj h H' * psuField h σ' * (psuConj h H')⁻¹ ∧
      (σ' = σ ∨ σ' * σ = 1) ∧ ∀ x, σ' x = x ↔ σ x = x := by
  have := h.finite
  have hψE : psuConj h H * psuField h σ * (psuConj h H)⁻¹ * y ∈ E := E.mul_mem hφE hyE
  have hψN : psuConj h H * psuField h σ * (psuConj h H)⁻¹ * y ∉ (psuConj h).range := by
    intro hm
    apply hφN
    have hm' := (psuConj h).range.mul_mem hm ((psuConj h).range.inv_mem hyN)
    rwa [mul_inv_cancel_right] at hm'
  have hψ3 : (psuConj h H * psuField h σ * (psuConj h H)⁻¹ * y) ^ 3 = 1 :=
    hE.2 _ hψE
  obtain ⟨σ', hσ', H', hψH⟩ := unitary_order_three_field_descent hq _ hψ3 hψN
  have h12 := CFSG.RankThree.PartTwo.Sec14.Item148Rank.ringAut_eq_or_mul_eq_one148 h.prime
    (by have := h.one_le; omega) h.card hσ hσ'
  refine ⟨σ', H', hσ', hψH, h12, ?_⟩
  rcases h12 with h1 | h1
  · intro x
    rw [h1]
  · have h2 : σ' = σ⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hinv : ∀ z, σ⁻¹ (σ z) = z := fun z => by simp
    have hinv' : ∀ z, σ (σ⁻¹ z) = z := fun z => by simp
    intro x
    rw [h2]
    constructor
    · intro hx
      calc σ x = σ (σ⁻¹ x) := by rw [hx]
        _ = x := hinv' x
    · intro hx
      calc σ⁻¹ x = σ⁻¹ (σ x) := by rw [hx]
        _ = x := hinv x

end CFSG.RankThree.PartTwo.Sec19
