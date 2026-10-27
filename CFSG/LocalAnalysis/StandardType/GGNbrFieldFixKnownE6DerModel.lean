module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixGeomDer
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Der
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Model

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.RecipeExcLang

set_option linter.unusedSectionVars false

theorem e6FixOn_isRoot_der {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (heven : Even n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    E6FixOn K (IsRoot Tag.E6) n p := by
  intro H hH f hf hord
  rw [chevH_false_eq_adjointGroup K Tag.E6] at hH
  subst hH
  have hrank : 0 < Tag.E6.rank := by decide
  obtain ⟨σ, hσ⟩ :=
    RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField (τ := Tag.E6) (K := K) hf
  have hσord : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut
      (τ := Tag.E6) (K := K) hrank σ, ← hσ, MulEquiv.orderOf_eq, hord]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσord
    exact hp.ne_one hσord.symm
  obtain ⟨hdvd, hcardfix⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
      Nat.prime_two hn hK σ
  rw [hσord] at hdvd hcardfix
  have hbig : 2 < Nat.card (fixSubfield σ) := by
    rw [hcardfix]
    obtain ⟨c, hc⟩ := hdvd
    have hc' : n / p = c := by rw [hc, Nat.mul_div_cancel_left c hp.pos]
    have hceven : Even c := by
      rcases Nat.even_mul.1 (hc ▸ heven) with h | h
      · exact absurd h (Nat.not_even_iff_odd.2 (hp.odd_of_ne_two hp2))
      · exact h
    have hc2 : 2 ≤ c := by
      obtain ⟨j, hj⟩ := hceven
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, mul_zero] at hc
        omega
      · omega
    rw [hc']
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc2
  let m : LargeEvenCenterQuot (adjointGroup Tag.E6 K) ≃* adjointGroup Tag.E6 K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  let m₀ : LargeEvenCenterQuot (adjointGroup Tag.E6 ↥(fixSubfield σ)) ≃*
      adjointGroup Tag.E6 ↥(fixSubfield σ) :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have hm : MulAut.congr m = autEquiv Tag.E6 K := rfl
  have hm₀ : MulAut.congr m₀ = autEquiv Tag.E6 ↥(fixSubfield σ) := rfl
  have hs : entrywiseAdjointAut Tag.E6 σ = MulAut.congr m f := by
    rw [← hσ, ← hm]
  refine ⟨↥(fixSubfield σ), inferInstance, inferInstance, hcardfix, ?_⟩
  intro H₀ hH₀
  rw [chevH_false_eq_adjointGroup ↥(fixSubfield σ) Tag.E6] at hH₀
  subst hH₀
  have hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 ↥(fixSubfield σ)
  refine ⟨hq.2.1, hq.2.2, ?_⟩
  refine ggFixGeom_of_transport_der m m₀ hs (E6FieldFix.fixE6DerEquiv σ) ?_ ?_
  · intro φ hφ hcomm
    obtain ⟨w, hw⟩ :=
      RecipeExcLang.exists_inndiagConj_of_mem_markID (τ := Tag.E6) (K := K) hφ
    have hwm : MulAut.congr m φ = inndiagConj Tag.E6 K w := by
      rw [← hw, ← hm]
    have hc : inndiagConj Tag.E6 K w * entrywiseAdjointAut Tag.E6 σ =
        entrywiseAdjointAut Tag.E6 σ * inndiagConj Tag.E6 K w := by
      have h1 := congrArg (MulAut.congr m) hcomm
      rwa [map_mul, map_mul, hwm, ← hs] at h1
    obtain ⟨w₀, hw₀⟩ := E6FieldFix.exists_inndiagConj_restrict_der hn hK hσ1 w hc
    refine ⟨(autEquiv Tag.E6 ↥(fixSubfield σ)).symm
      (inndiagConj Tag.E6 ↥(fixSubfield σ) w₀), ?_, ?_⟩
    · exact RecipeExcLang.inndiagConj_mem_markID w₀
    · intro y
      have h0 : MulAut.congr m₀ ((autEquiv Tag.E6 ↥(fixSubfield σ)).symm
          (inndiagConj Tag.E6 ↥(fixSubfield σ) w₀)) =
          inndiagConj Tag.E6 ↥(fixSubfield σ) w₀ := by
        rw [← hm₀]
        exact MulEquiv.apply_symm_apply _ _
      rw [hwm, h0]
      exact hw₀ y
  · intro φ hφ hcomm hfix
    obtain ⟨w, hw⟩ :=
      RecipeExcLang.exists_inndiagConj_of_mem_markID (τ := Tag.E6) (K := K) hφ
    have hwm : MulAut.congr m φ = inndiagConj Tag.E6 K w := by
      rw [← hw, ← hm]
    have hfixw : ∀ x : ↥(ggFixDer (entrywiseAdjointAut Tag.E6 σ)),
        inndiagConj Tag.E6 K w (x : adjointGroup Tag.E6 K) = x := by
      intro x
      rw [← hwm]
      exact hfix x
    have hw1 : inndiagConj Tag.E6 K w = 1 :=
      E6FieldFix.eq_one_of_inndiagConj_fixes_der hbig w hfixw
    have h1 : MulAut.congr m φ = 1 := by rw [hwm, hw1]
    exact (MulAut.congr m).injective (by rw [h1, map_one])

theorem e6_fixStd_der {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (heven : Even n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.E6.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false))
    (hord : orderOf f = p) :
    LargeEvenRecipeChevalley Tag.E6.cartan (2 ^ (n / p)) false fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        ∃ θ₀ : ggFixDer f ≃* R₀,
          GGFixGeom
            (LargeEvenChevIDImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) f I₀
            θ₀ := by
  have h := (e6FixOn_isRoot_der hn hK heven hp hp2).of_eq (largeEvenIsRoot_eq_isRoot Tag.E6).symm
  obtain ⟨k, _, _, hk, hconcl⟩ :=
    h (LargeEvenChevH Tag.E6.cartan K false) (largeEvenChevH_eq _ K false) f hf hord
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  obtain ⟨hs, hna, θ₀, hg⟩ :=
    hconcl (LargeEvenChevH Tag.E6.cartan k false) (largeEvenChevH_eq _ k false)
  refine ⟨hs, hna, θ₀, ?_⟩
  rw [largeEvenChevIDImage_eq, largeEvenChevIDImage_eq]
  exact hg

end CFSG.StandardType

end
