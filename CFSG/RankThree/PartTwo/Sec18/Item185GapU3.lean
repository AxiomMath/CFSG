module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterLin
import CFSG.RankThree.PartTwo.KFacts.K71PSU3
import CFSG.RankThree.PartTwo.Sec18.Item185PGL3

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField unitary_order_three_field_descent
  exists_card_fixedField_of_orderOf_eq_three bar_coe_fixedField puHom ker_puHom mem_range_puHom_iff)
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk)

private theorem mem_fixedSubgroup_gapU3 {S : Type} [Group S] (σ : MulAut S) (x : S) :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

private theorem fixedSubgroup_conj_eq {S : Type} [Group S] (g τ : MulAut S) :
    fixedSubgroup (g * τ * g⁻¹) = (fixedSubgroup τ).map (MulEquiv.toMonoidHom g) := by
  ext y
  rw [mem_fixedSubgroup_gapU3, Subgroup.mem_map]
  constructor
  · intro hy
    rw [MulAut.mul_apply, MulAut.mul_apply] at hy
    refine ⟨g⁻¹ y, ?_, ?_⟩
    · rw [mem_fixedSubgroup_gapU3]
      apply MulEquiv.injective g
      rw [hy, MulAut.apply_inv_self _ g]
    · exact MulAut.apply_inv_self _ g y
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixedSubgroup_gapU3] at hx
    rw [MulAut.mul_apply, MulAut.mul_apply]
    show g (τ (g⁻¹ (g x))) = g x
    rw [MulAut.inv_apply_self _ g, hx]

private theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h4 : 2 ^ (2 * (k + 1) + 1) = 2 ^ (2 * k + 1) * 4 := by ring
    rw [h4, Nat.mul_mod, ih] <;> norm_num

private theorem hasNormalSimpleCentralizer_fixedSubgroup_psuField {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hodd : Odd f) (h9 : 9 ≤ f) {τ : K ≃+* K}
    (hτ : orderOf τ = 3) :
    HasNormalSimpleCentralizer (fixedSubgroup (psuField h τ)) := by
  obtain ⟨f₀, hf, hf₁, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hτ
  have h₀ : UnitaryFieldData 2 f₀ (fixedField τ) := ⟨Nat.prime_two, hf₁, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  have hker := ker_puHom h hf h₀ hbar
  have hodd₀ : Odd f₀ := by
    rw [hf] at hodd
    exact (Nat.odd_mul.mp hodd).2
  have hf₃ : 3 ≤ f₀ := by omega
  have hq2 : 2 < 2 ^ f₀ :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf₃)
  have hm : Sec4.ModThree false (2 ^ f₀) := two_pow_mod_three_of_odd hodd₀
  have hK₀ : Sec4.PiField false 2 f₀ (fixedField τ) :=
    ⟨Nat.prime_two, hf₁, by rw [hcard, Sec4.piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
  have hRange : (puHom h hf h₀ hbar).range = fixedSubgroup (psuField h τ) := by
    ext y
    exact mem_range_puHom_iff h hf h₀ hbar y
  let Ψ : projImage (Sec4.glPi false 3 (2 ^ f₀) (fixedField τ)) ≃* (puHom h hf h₀ hbar).range :=
    (statedProjEquivMapMk _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange (puHom h hf h₀ hbar)))
  have e₁ : fixedSubgroup (psuField h τ) ≃*
      projImage (Sec4.glPi false 3 (2 ^ f₀) (fixedField τ)) :=
    (MulEquiv.subgroupCongr hRange).symm.trans Ψ.symm
  exact HasNormalSimpleCentralizer.of_mulEquiv e₁.symm
    (hasNormalSimpleCentralizer_projImage_glPi hK₀ hq2 hm)

theorem gapU3Field_fixedFacts :
    ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), Odd f → 9 ≤ f → 3 ∣ f →
      ∀ σ : MulAut (unitaryPSU h 3), σ ^ 3 = 1 → σ ∉ (psuConj h).range → FixedFactsAt σ := by
  intro f K _ h hodd h9 _ σ hσ3 hσD
  have hq : 2 < 2 ^ f :=
    lt_of_lt_of_le (show 2 < 2 ^ 2 by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (show 2 ≤ f by omega))
  obtain ⟨τ, hτ3, g, rfl⟩ := unitary_order_three_field_descent hq σ hσ3 hσD
  unfold FixedFactsAt
  refine Or.inl ?_
  exact HasNormalSimpleCentralizer.of_mulEquiv
    ((Subgroup.equivMapOfInjective (fixedSubgroup (psuField h τ))
        (MulEquiv.toMonoidHom (psuConj h g)) (MulEquiv.injective (psuConj h g))).trans
      (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq (psuConj h g) (psuField h τ)).symm))
    (hasNormalSimpleCentralizer_fixedSubgroup_psuField h hodd h9 hτ3)

theorem gapU3Field_holds : GapU3Field := gapU3Field_fixedFacts

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
