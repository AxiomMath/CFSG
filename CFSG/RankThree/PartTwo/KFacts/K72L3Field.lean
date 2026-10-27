module

public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
public import CFSG.RankThree.PartTwo.Sec8.Notation
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

theorem fixedData_of_mulEquiv_projSL {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K % 3 = 2) (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 K)
    (α : MulAut X) (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card X) ∧
      ∃ x₀ y₀ : X, α x₀ = x₀ ∧ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 K
  have hβ3 : MulAut.congr (e.trans φ) α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hD : MulAut.congr (e.trans φ) α ∉ linearAutGroup 3 K := fun h =>
    hout ((isInnerAut_congr (e.trans φ) α).mp (isInnerAut_of_mem_linearAutGroup hK h))
  obtain ⟨σ, hσ, H, hβH⟩ :=
    linear_order_three_field_descent le_rfl (MulAut.congr (e.trans φ) α) hβ3 hD
  have hτ : MulAut.congr ((e.trans φ).trans (conjAut 3 K H)⁻¹) α = fieldAut 3 K σ := by
    rw [congr_trans_mulAut, hβH]
    group
  obtain ⟨h₁, h₂⟩ := fixedData_linear hK hσ
  rw [← hτ] at h₁ h₂
  exact fixedData_of_congr _ α h₁ h₂

theorem fixedData_of_mulEquiv_projSU {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hq : 2 ^ (3 * n) % 3 = 1) (e : X ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 (3 * n))
    (α : MulAut X) (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card X) ∧
      ∃ x₀ y₀ : X, α x₀ = x₀ ∧ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  have h : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  have hβ3 : MulAut.congr (e.trans φ.symm) α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have hD : MulAut.congr (e.trans φ.symm) α ∉ (psuConj h).range := fun hm =>
    hout ((isInnerAut_congr (e.trans φ.symm) α).mp (isInnerAut_of_mem_psuConj_range h hq hm))
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  obtain ⟨σ, hσ, H, hβH⟩ :=
    unitary_order_three_field_descent hq2 (MulAut.congr (e.trans φ.symm) α) hβ3 hD
  have hτ : MulAut.congr ((e.trans φ.symm).trans (psuConj h H)⁻¹) α = psuField h σ := by
    rw [congr_trans_mulAut, hβH]
    group
  obtain ⟨h₁, h₂⟩ := fixedData_unitary h hq hσ
  rw [← hτ] at h₁ h₂
  exact fixedData_of_congr _ α h₁ h₂

theorem fixedData_of_isoLThreeMinusPi {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Sec8.IsoLThreeMinusPi X 2 (3 * n)) (α : MulAut X) (hα : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup X, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card X) ∧
      ∃ x₀ y₀ : X, α x₀ = x₀ ∧ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · exact fixedData_of_mulEquiv_projSU hn hq e α hα hout
  · refine fixedData_of_mulEquiv_projSL ?_ e α hα hout
    rwa [GaloisField.card 2 (3 * n) (by omega)]

theorem exists_ne_of_sylow_of_isoLThreeMinusPi {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 1 ≤ n) (hX : Sec8.IsoLThreeMinusPi X 2 (3 * n)) (α : MulAut X) (hα : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) (S : Sylow 3 X) : ∃ y ∈ (S : Subgroup X), α y ≠ y := by
  obtain ⟨M, hM, h3M⟩ := (fixedData_of_isoLThreeMinusPi hn hX α hα hout).1
  exact exists_ne_of_sylow_of_card_dvd α hM h3M S

theorem exists_inverting_of_isoLThreeMinusPi {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 1 ≤ n) (hX : Sec8.IsoLThreeMinusPi X 2 (3 * n)) (α : MulAut X) (hα : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) (x : X) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxα : α x = x) :
    ∃ y : X, α y = y ∧ y * x * y⁻¹ = x⁻¹ := by
  obtain ⟨x₀, y₀, hx₀, hy₀, hx₀3, hx₀1, hinv⟩ :=
    (fixedData_of_isoLThreeMinusPi hn hX α hα hout).2
  obtain ⟨y, hy, hyx⟩ := exists_conj_eq_inv_of_isCyclic_sylow
    (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X))
    (isCyclic_sylow_three_of_isoLThreeMinusPi hn hX) hx₀ hy₀ hx₀3 hx₀1 hinv hxα hx3 hx1
  exact ⟨y, hy, hyx⟩

end CFSG.RankThree.PartTwo.KFacts
