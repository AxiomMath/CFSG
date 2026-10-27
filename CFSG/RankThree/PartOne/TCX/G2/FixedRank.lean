module

public import CFSG.RankThree.PartOne.TCX.G2.Assembly
public import CFSG.RankThree.PartOne.TCX.RankInterface

public section

namespace CFSG.RankThree.PartOne.TCX.G2

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.PartOne.KLC (pRank_congr_mulEquiv two_le_pRank_of_orth_roots g2Orth_commute
  dvd_sub_one_or_dvd_add_one)

open CFSG.RankThree.PartOne.K128 (dvd_card_of_pRank_pos pRank_le_one_G2 dvd_sq_sub_one_of_dvd_pow)

open CFSG.RankThree.Chevalley (even_G2_canonical_field_centralizer_all_orders)

open CFSG.LieType.Steinberg.Adjoint (isPerfect_g2_of_three_le_card)

open CFSG.RankThree.PartOne.TCX

section Main


theorem fixedRankT_G2 : FixedRankT .G2 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, σ, φ, hKcard, hσord, hφα⟩ := g2_stdForm hp hp5 hf₀ hM hαp hαinn
  have hf1 : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have hf : 2 ≤ p * f₀ := by
    have : 2 ≤ p := hp.two_le
    nlinarith
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1
      hKcard
  have hpG : 2 ≤ CFSG.pRank p (adjointGroup Tag.G2 K) := by
    rw [← pRank_congr_mulEquiv φ hp.one_lt]
    exact hpr
  have hdvdG : p ∣ Nat.card (adjointGroup Tag.G2 K) := dvd_card_of_pRank_pos hp (by omega)
  have hd : p ∣ Nat.card K ^ 2 - 1 := by
    by_contra hnd
    have := pRank_le_one_G2 K hp hp5 hKcard hf1 hdvdG hnd
    omega
  obtain ⟨-, -, -, hJC1, -⟩ := even_G2_canonical_field_centralizer_all_orders hf hKcard σ
  have hK₀card : Nat.card (fixSubfield σ) = 2 ^ f₀ := by
    obtain ⟨-, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two hf1
      hKcard σ
    rw [hc, hσord, Nat.mul_div_cancel_left f₀ hp.pos]
  have hq2 : 2 ≤ 2 ^ f₀ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  have hpq : ¬ p ∣ 2 ^ f₀ := by
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hd' : p ∣ (2 ^ f₀) ^ 2 - 1 := by
    have hKK : Nat.card K = (2 ^ f₀) ^ p := by rw [hKcard, mul_comm, pow_mul]
    rw [hKK] at hd
    exact dvd_sq_sub_one_of_dvd_pow hp (by omega) hq2 hpq hd
  have hq4 : 3 ≤ 2 ^ f₀ := by
    by_contra hlt
    have h2 : 2 ^ f₀ = 2 := by omega
    rw [h2] at hd'
    have : p ∣ 3 := by simpa using hd'
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have e3 : ↥(fixSub (entrywiseAdjointAut Tag.G2 σ)) ≃* ↥(fixedFieldImage Tag.G2 σ) :=
    (Subgroup.equivMapOfInjective _ (adjointGroup Tag.G2 K).subtype
      (adjointGroup Tag.G2 K).subtype_injective).trans (MulEquiv.subgroupCongr hJC1)
  have e1 : ↥(fixSub α) ≃* ↥(fixSub (entrywiseAdjointAut Tag.G2 σ)) :=
    (fixIso φ α).trans (MulEquiv.subgroupCongr (by rw [hφα]))
  have eFix : ↥(fixSub α) ≃* adjointGroup Tag.G2 (fixSubfield σ) :=
    (e1.trans e3).trans (fixedFieldImageEquiv (τ := Tag.G2) σ).symm
  have hperf : Group.IsPerfect ↥(fixSub α) := by
    have : Group.IsPerfect (adjointGroup Tag.G2 (fixSubfield σ)) :=
      isPerfect_g2_of_three_le_card (fixSubfield σ) (by rw [hK₀card]; exact hq4)
    exact Group.IsPerfect.ofSurjective (f := eFix.symm.toMonoidHom) eFix.symm.surjective
  have hres : fixRes α = fixSub α := fixRes_eq_fixSub_of_perfect hperf
  have hdK₀ : p ∣ Nat.card (fixSubfield σ) ^ 2 - 1 := by
    rw [hK₀card]
    exact hd'
  have : CharP (fixSubfield σ) 2 := ⟨fun x => by
    rw [← (fixSubfield σ).subtype.injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff K 2 x⟩
  exact two_le_pRank_of_orth_roots (τ := Tag.G2) (K := fixSubfield σ) g2Orth_commute hp hdK₀
    ((MulEquiv.subgroupCongr hres).trans eFix)

end Main

end CFSG.RankThree.PartOne.TCX.G2
