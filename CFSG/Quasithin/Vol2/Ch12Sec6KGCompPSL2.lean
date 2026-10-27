module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompPSL2B
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartTwo.KFacts

variable {F : Type} [Field F] [Finite F]

theorem eq_of_dvd_three_or_five {n : ℕ} (h : n ∣ 3 ∨ n ∣ 5) : n = 1 ∨ n = 3 ∨ n = 5 := by
  rcases h with h | h
  · rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h <;> omega
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h | h <;> omega

theorem not_autConf_psl2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : f = 1 ∨ f = 2)
    (hFc : Nat.card F = p ^ f) (hq : p ^ f ≠ 3 ∧ p ^ f ≠ 5 ∧ p ^ f ≠ 9 ∧ p ^ f ≠ 11)
    {ν : MulAut (PSL2 F)} {Lb Pb : Subgroup (MulAut (PSL2 F))} (h : AutConf (PSL2 F) ν Lb Pb) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hFc])
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hF : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, by omega, hFc⟩
  have hqge : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have hq3 : 3 < Nat.card F := by rw [hFc]; have := hq.1; omega
  have hZ := psl2_center_eq_bot F
  obtain ⟨c, hc, hc3⟩ := h.exists_innerPart_three hZ fun α hα =>
    mem_range_conj_of_pow_three_eq_one hF hp hFc hf hα
  have hνc : ν c = c := h.fix_of_mem_innerPart hZ hc
  by_cases hD : ν ∈ (pglAction F).range
  · obtain ⟨g, rfl⟩ := hD
    have hg : BenderSuzuki.PFAppendixIII.IsInvolution g :=
      ⟨fun h1 => h.ne_one (by rw [h1, map_one]),
        pglAction_injective hF hq3 (by rw [map_pow, h.sq, map_one])⟩
    have hdiv : ∀ x : PSL2 F, Odd (orderOf x) → pglAction F g x = x⁻¹ →
        orderOf x = 1 ∨ orderOf x = 3 ∨ orderOf x = 5 := fun x ho hi =>
      eq_of_dvd_three_or_five ((h.inv x ho hi).imp orderOf_dvd_of_pow_eq_one
        orderOf_dvd_of_pow_eq_one)
    obtain ⟨x₁, hx₁, hi₁⟩ := exists_pglAction_inv_split hF hq3 hg
    obtain ⟨x₂, hx₂, hi₂⟩ := exists_pglAction_inv_nonsplit hF hq3 hg
    obtain ⟨k, hk⟩ : Odd (Nat.card F) := by rw [hFc]; exact hpodd.pow
    have hk1 : (Nat.card F - 1) / 2 = k := by omega
    have hk2 : (Nat.card F + 1) / 2 = k + 1 := by omega
    rw [hk1] at hx₁
    rw [hk2] at hx₂
    have hq7 : Nat.card F = 7 := by
      rcases Nat.even_or_odd k with hke | hko
      · have := hdiv x₂ (by rw [hx₂]; exact hke.add_one) hi₂
        rw [hx₂] at this
        have := hq.2.1
        have := hq.2.2.1
        rw [← hFc] at *
        omega
      · have := hdiv x₁ (by rw [hx₁]; exact hko) hi₁
        rw [hx₁] at this
        have := hq.2.2.2
        rw [← hFc] at *
        omega
    have hp7 : p = 7 := by
      rw [hFc] at hq7
      rcases hf with rfl | rfl
      · simpa using hq7
      · exfalso
        have : 3 * 3 ≤ p ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hp3 hp3
        omega
    by_cases hgJ : g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
    · obtain ⟨t, rfl⟩ := hgJ
      rw [pglAction_toPGL] at hνc
      have ht : orderOf t = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        refine orderOf_eq_prime ?_ ?_
        · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
          rw [map_pow, hg.2, map_one]
        · intro h1
          exact hg.1 (by rw [h1, map_one])
      have hcomm : Commute t c := by
        rw [MulAut.conj_apply] at hνc
        exact (mul_inv_eq_iff_eq_mul.mp hνc)
      exact psl2_seven_not_commute hq7 ht hc3 hcomm
    · obtain ⟨x, hx, hi⟩ :=
        exists_pglAction_inv_unipotent hF hq3 (by rw [hq7]) hg hgJ
      have := hdiv x (by rw [hx]; exact hpodd) hi
      omega
  · obtain ⟨σ, hσ, g, hνeq⟩ := linear_two_prime_order_field_descent Nat.prime_two ν
      (orderOf_eq_prime h.sq h.ne_one) hD
    have hf2 : f = 2 := by
      rcases hf with rfl | rfl
      · exfalso
        have := ringAut_eq_one hp (by rw [hFc, pow_one]) σ
        rw [this, orderOf_one] at hσ
        omega
      · rfl
    subst hf2
    set e : PSL2 F ≃* PSL2 F := (pglAction F g)⁻¹ with he
    have hcongr : MulAut.congr e ν = psl2FieldAut F σ := by
      refine MulEquiv.ext fun x => ?_
      rw [MulAut.congr_apply, hνeq]
      change (pglAction F g)⁻¹ ((pglAction F g * psl2FieldAut F σ * (pglAction F g)⁻¹)
        ((pglAction F g) x)) = _
      simp [MulAut.mul_apply]
    have h' := h.map e
    rw [hcongr] at h'
    by_cases hp35 : p ≠ 3 ∧ p ≠ 5
    · exact not_autConf_fieldAut_of_ne hp2 hp35 hσ h'
    · rcases (by omega : p = 3 ∨ p = 5) with rfl | rfl
      · exact hq.2.2.1 (by norm_num)
      · exact not_autConf_fieldAut_five hFc h'

theorem comp12626L2Odd_holds : Comp12626L2Odd := by
  intro Q _ K L P T v hQ h p f hp hp2 hf hL2
  have := hQ.finite
  by_cases h11 : p = 11 ∧ f = 1
  · exact h11
  exfalso
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hA := h.autConf
  by_cases h5 : p = 5 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨e⟩ := CFSG.QuasithinUnique.Setup.Family.alternating_five_of_model_five hL2
    exact not_autConf_alt5 (hA.map e)
  by_cases h9 : p = 3 ∧ f = 2
  · obtain ⟨rfl, rfl⟩ := h9
    obtain ⟨e⟩ := CFSG.QuasithinUnique.Setup.Family.alternating_six_of_model_nine hL2
    obtain ⟨E, hE, hE9⟩ := exists_E9_alt6
    exact not_autConf_alt6 (hA.map e) (h.card_map_rhoP_eq_nine hQ e
      (fun z hz => eq_one_of_mem_center_alt (by norm_num) hz) hE hE9)
  obtain ⟨hadm, F, _, _, hFc, ⟨e⟩⟩ := hL2
  have hq3 : p ^ f ≠ 3 := fun h3 => hadm.2.2.2.2 (by rw [h3])
  have hq : p ^ f ≠ 3 ∧ p ^ f ≠ 5 ∧ p ^ f ≠ 9 ∧ p ^ f ≠ 11 := by
    refine ⟨hq3, ?_, ?_, ?_⟩ <;> rcases hf with rfl | rfl
    · rw [pow_one]; omega
    · have : 3 * 3 ≤ p ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hp3 hp3
      omega
    · rw [pow_one]
      rintro rfl
      exact absurd hp (by norm_num)
    · intro h9'
      apply h9
      refine ⟨?_, rfl⟩
      have h4 : p < 4 := by
        by_contra h4
        have : 4 * 4 ≤ p ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
        omega
      interval_cases p
      simp_all
    · rw [pow_one]; omega
    · intro h11'
      have h4 : p < 4 := by
        by_contra h4
        have : 4 * 4 ≤ p ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
        omega
      interval_cases p
      simp_all
  exact not_autConf_psl2 hp hp2 hf hFc hq (hA.map
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm))

end CFSG.Quasithin.H13.S126C
