module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2CaseIIb
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2CaseIISmall
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2CaseIII
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2InnerBig
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2InnerEleven
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Model
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupInner
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSp4
public import CFSG.OddTranspositions.TheoremTwo.TheoremFourNine.LinearBranches

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
  CFSG.ComponentClassification.AutL2Facts

private theorem odd_eq_seven_or_eleven_or_thirteen_le {q : ℕ} (hq : Odd q) (h7 : 7 ≤ q)
    (h9 : q ≠ 9) : q = 7 ∨ q = 11 ∨ 13 ≤ q := by
  obtain ⟨k, hk⟩ := hq
  by_cases h13 : 13 ≤ q
  · exact Or.inr (Or.inr h13)
  · have hlt : q < 13 := by omega
    interval_cases q
    · exact Or.inl rfl
    · omega
    · exact absurd rfl h9
    · omega
    · exact Or.inr (Or.inl rfl)
    · omega

theorem l2CaseII_pgl2 {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hKcard : Nat.card K = p ^ f) (hq : 7 ≤ p ^ f) (hq9 : p ^ f ≠ 9)
    {t β : PGL2 K} (htJ : t ∈ pslRange K) (hβJ : β ∉ pslRange K) (ht : t * t = 1) (ht1 : t ≠ 1)
    (hβ : β * β = 1) (hcomm : t * β = β * t) : L2CaseII (pslRange K) t β := by
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hparrott : ParrottGen (pslRange K) t β := by
    rcases odd_eq_seven_or_eleven_or_thirteen_le hqodd hq hq9 with h7 | h11 | h13
    · exact parrottGen_pgl2_small (Or.inl (hKcard.trans h7)) htJ hβJ ht ht1 hβ hcomm
    · exact parrottGen_pgl2_small (Or.inr (hKcard.trans h11)) htJ hβJ ht ht1 hβ hcomm
    · exact parrottGen_pgl2_of_thirteen_le hp hp2 hKcard h13 htJ hβJ ht ht1 hβ hcomm
  exact ⟨hparrott, pslRange_le_quadY_sup hp hp2 hKcard hq htJ hβJ ht ht1 hβ hcomm⟩

theorem l2OuterFacts_pGammaL2 {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKcard : Nat.card K = p ^ f) (hq : 7 ≤ p ^ f)
    (hq9 : p ^ f ≠ 9) : L2OuterFacts (pGammaL2PSLRange K) := by
  intro t β htI hβI ht ht1 hβ hcomm
  obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff K t).mp htI
  set u : PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL y with hu_def
  have hu : SemidirectProduct.inl u = t := by simpa [u] using hy
  have huJ : u ∈ pslRange K := ⟨y, rfl⟩
  by_cases hβlin : β.right = 1
  · set β₀ : PGL2 K := β.left with hβ₀_def
    have hβinl : β = SemidirectProduct.inl β₀ := by
      simpa [β₀] using eq_inl_of_right_eq_one hβlin
    have hβ₀J : β₀ ∉ pslRange K := by
      intro hmem
      apply hβI
      obtain ⟨z, hz⟩ := hmem
      rw [hβinl, ← hz]
      exact (range_incl K).symm ▸ MonoidHom.mem_range.mpr ⟨z, rfl⟩
    have hu2 : u * u = 1 := by
      apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
      rw [map_mul, map_one, hu, ht]
    have hu1 : u ≠ 1 := by
      intro h1
      apply ht1
      rw [← hu, h1, map_one]
    have hβ₀2 : β₀ * β₀ = 1 := by
      apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
      rw [map_mul, map_one, ← hβinl, hβ]
    have hcomm₀ : u * β₀ = β₀ * u := by
      apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
      rw [map_mul, map_mul, hu, ← hβinl, hcomm]
    have hII := l2CaseII_pgl2 (K := K) hp hp2 hKcard hq hq9 huJ hβ₀J hu2 hu1 hβ₀2 hcomm₀
    have hmapRange : (pslRange K).map
        (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) = pGammaL2PSLRange K := by
      change (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
        (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) = pGammaL2PSLRange K
      rw [MonoidHom.map_range]
      rfl
    have hmap := L2CaseII.map (f := (SemidirectProduct.inl : PGL2 K →* PGammaL2 K))
      (SemidirectProduct.inl_injective (φ := pgl2FieldAut K)) hII
    rw [hmapRange, hu, ← hβinl] at hmap
    exact Or.inl hmap
  · have hβright : β.right ≠ 1 := hβlin
    set σ : K ≃+* K := β.right with hσ_def
    have hσne : σ ≠ 1 := by simpa [σ] using hβright
    have hσ2 : σ * σ = 1 := by
      have h := congrArg SemidirectProduct.right hβ
      simpa [σ] using h
    have hσ : orderOf σ = 2 := orderOf_eq_prime (by rwa [pow_two]) hσne
    obtain ⟨K₀, -, hK₀card, -⟩ := exists_fixed_subfield σ hσ
    set r : ℕ := Nat.card K₀ with hr_def
    have hKcardr : Nat.card K = r ^ 2 := by simpa [r] using hK₀card
    have hsq : r ^ 2 = p ^ f := by rw [← hKcardr, hKcard]
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with hf0 | hfpos
      · rw [hf0, pow_zero] at hq
        omega
      · exact hfpos
    have hqpp : IsOddPrimePower (p ^ f) := by
      rw [← hKcard]
      exact isOddPrimePower_of hp hp2 hf hKcard
    have hr : IsOddPrimePower r := by
      simpa [r] using CFSG.OddTranspositions.QZ.isOddPrimePower_of_sq
        (F := K₀) (q := p ^ f) hqpp hsq
    have hrodd : Odd r := by
      obtain ⟨p', n, hp', hpo, -, hrn⟩ := hr
      rw [hrn]
      exact hpo.pow
    have hrne3 : r ≠ 3 := by
      intro h3
      apply hq9
      rw [← hKcard, hKcardr, h3]
      norm_num
    have hr3 : 3 ≤ r := by
      by_contra h
      have hle : r ≤ 2 := by omega
      have h7 : 7 ≤ r ^ 2 := by rw [hsq]; exact hq
      nlinarith
    have hr5 : 5 ≤ r := by
      obtain ⟨k, hk⟩ := hrodd
      omega
    exact Or.inr (l2CaseIII_pGammaL2 (r := r) hr hr5 hKcardr htI hβright ht ht1 hβ hcomm)

theorem l2AutFacts_psl2 {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hKcard : Nat.card K = p ^ f) (hq : 7 ≤ p ^ f)
    (hq9 : p ^ f ≠ 9) : L2AutFacts (PSL2 K) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hfpos
    · rw [hf0, pow_zero] at hq
      omega
    · exact hfpos
  have h5 : 5 ≤ p ^ f := by omega
  have hmodel : Blueprint.LieModel (PSL2 K) .PSL 2 p f :=
    CFSG.ComponentClassification.Sp4Rec.lieModel_projectiveSL_two (F := K) hp hf hKcard h5
  refine ⟨?_, ?_⟩
  · intro W hW2 hW4
    exact footeFourgroupInner (PSL2 K) (Or.inr ⟨p, f, hp, hp2, hf, h5, hmodel⟩) W hW2 hW4
  · let E : MulAut (PSL2 K) ≃* PGammaL2 K := autEquiv (MulEquiv.refl (PSL2 K))
    have hmap : (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range.map E.toMonoidHom =
        pGammaL2PSLRange K := map_autEquiv_innAut (e := MulEquiv.refl (PSL2 K))
    have hsymm : (pGammaL2PSLRange K).map
        (E.symm : PGammaL2 K →* MulAut (PSL2 K)) =
        (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range :=
      (Subgroup.map_symm_eq_iff_map_eq (H :=
        (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range)
        (K := pGammaL2PSLRange K) (e := E.symm)).mp (by simpa using hmap)
    have houter := L2OuterFacts.map (l2OuterFacts_pGammaL2 hp hp2 hKcard hq hq9) E.symm
    simpa [hsymm] using houter

theorem l2InnerFacts_psl2 {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hKcard : Nat.card K = p ^ f) (hq : 11 ≤ p ^ f) :
    L2InnerFacts (PSL2 K) := by
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  rcases odd_eq_seven_or_eleven_or_thirteen_le hqodd (by omega) (by omega) with h7 | h11 | h13
  · omega
  · exact l2InnerFacts_psl2_eleven (K := K) (hK := hKcard.trans h11)
  · exact l2InnerFacts_psl2_of_thirteen_le hp hp2 hKcard h13

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
