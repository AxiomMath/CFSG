module

public import CFSG.RankThree.PartTwo.Sec4.E27.L3FUnitaryPair
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoL4
public import CFSG.RankThree.PartTwo.Sec4.E27.L3FAbstract
public import CFSG.RankThree.PartTwo.Sec4.E27.L3FUnitaryIso

public section

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff)

theorem seitz27_unitaryPSU_cubic (hA : Sec19.SeitzThreeLThreePi)
    {m : ℕ} (hm : 3 ≤ m) (hmod : 2 ^ m % 3 = 2) {K : Type} [Field K]
    (h : UnitaryFieldData 2 (3 * m) K) : Seitz27 (unitaryPSU h 3) := by
  intro E hE hc27
  have hc : Nat.card E = 3 ^ 3 := by rw [hc27]; norm_num
  have := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2m : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hQ : 2 ^ (3 * m) % 3 = 2 := by
    rw [pow_mul', Nat.pow_mod, hmod]
  have hq : 2 < 2 ^ (3 * m) := by
    calc 2 < 8 := by norm_num
      _ ≤ 2 ^ m := h2m
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (3 : K) ≠ 0 := Sec19.three_ne_zero_of_unitaryFieldData h hQ
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ := center_unitaryPSU_three_eq_bot h hq
  have hnN := not_le_psuConj_range_of_card h3 hE (by omega)
  obtain ⟨phi, hphiE, hphiN⟩ : ∃ phi ∈ E, phi ∉ (psuConj h).range := by
    by_contra hcon
    push Not at hcon
    exact hnN fun x hx => hcon x hx
  obtain ⟨σ, hσ3, H, hphiH⟩ := unitary_order_three_field_descent hq phi (hE.2 phi hphiE) hphiN
  subst hphiH
  have hcardA := card_inf_psuConj_range_eq_nine h3 hq hE hc27
  obtain ⟨y, hyA, hy1⟩ : ∃ y ∈ E ⊓ (psuConj h).range, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : E ⊓ (psuConj h).range = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot] at hcardA
    omega
  obtain ⟨σ', H', hσ'3, hψH, -, hfix'⟩ :=
    Sec19.exists_second_field_element_psu hq hE hσ3 hphiE hphiN hyA.1 hyA.2
  obtain ⟨e₀, hfe, he₀, hkcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ3
  have hem : e₀ = m := by omega
  have h₀ : UnitaryFieldData 2 m (fixedField σ) :=
    ⟨h.prime, by omega, by rw [hkcard, hem]⟩
  have hbar := bar_coe_fixedField h (f₀ := m) rfl h₀
  have hk : ∀ x, x ∈ fixedField σ ↔ σ x = x := mem_fixedField_iff σ
  have hk' : ∀ x, x ∈ fixedField σ ↔ σ' x = x := fun x => (hk x).trans (hfix' x).symm
  have hψE : psuConj h H' * psuField h σ' * (psuConj h H')⁻¹ ∈ E := by
    rw [← hψH]
    exact E.mul_mem hphiE hyA.1
  have hψN : psuConj h H' * psuField h σ' * (psuConj h H')⁻¹ ∉ (psuConj h).range := by
    intro hm'
    apply hphiN
    rw [← hψH] at hm'
    have := (psuConj h).range.mul_mem hm' ((psuConj h).range.inv_mem hyA.2)
    rwa [mul_inv_cancel_right] at this
  have hφ1 : psuConj h H * psuField h σ * (psuConj h H)⁻¹ ≠ 1 := fun h1 =>
    hphiN (by rw [h1]; exact one_mem _)
  have hψ1 : psuConj h H' * psuField h σ' * (psuConj h H')⁻¹ ≠ 1 := fun h1 =>
    hψN (by rw [h1]; exact one_mem _)
  have hne := conj_moves_of_second h hQ hq hσ3 hk hk' hyA.2 hy1 hψH
  have hgen := lineU_sup_eq_top h h₀ hbar rfl (by omega) hne
  exact seitzHyperGamma_eq_top_of_two_subfield_lines hA (p := 2) (m := m) (by omega)
    (by omega) (by omega) hZ hE hc hphiE hψE hφ1 hψ1
    (isoLThreePi_lineU h h₀ hbar hmod H) (isoLThreePi_lineU h h₀ hbar hmod H')
    (lineU_invariant h h₀ hbar h3 hq hE hc27 hσ3 hk hphiE hphiN)
    (lineU_invariant h h₀ hbar h3 hq hE hc27 hσ'3 hk' hψE hψN)
    (fun l hl => fieldLineU_fixes_lineU h h₀ hbar hq hk hl)
    (fun l hl => fieldLineU_fixes_lineU h h₀ hbar hq hk' hl)
    (lineU_ker h h₀ hbar h3 hQ hq hE hc27 hσ3 hk hphiE hphiN)
    (lineU_ker h h₀ hbar h3 hQ hq hE hc27 hσ'3 hk' hψE hψN) hgen

end CFSG.RankThree.PartTwo.Sec4.E27
