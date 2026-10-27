module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Lift
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34UniqueP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoGood_vector
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (h3 : 3 ∈ D.sig)
    (hW : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    ∃ u₀ ∈ wTil V₀ V hV L, u₀ ≠ 1 ∧
      ∀ R : Subgroup (MulAut (Vtil V₀ V hV)), R ≤ Mbar D.M V₀ V hV → IsElemAbelian 3 R →
        (∀ r ∈ R, r u₀ = u₀) → Nat.card ↥R ≤ 3 := by
  classical
  obtain ⟨w, hw⟩ := not_forall.1 hW
  rw [not_imp] at hw
  obtain ⟨hwW, hw⟩ := hw
  rw [not_imp] at hw
  obtain ⟨hw1, hwU⟩ := hw
  have hwV : w ∈ V :=
    (preTil_le V₀ V hV (wTil V₀ V hV L)) (by simpa [wSub] using hwW)
  have h3eq := s16h_pRank_eq_three D S hr3 h3
  have h3rank : 3 ≤ CFSG.Open.pRank 3 D.M := le_of_eq h3eq.symm
  have hw0 : w ∉ V₀ := by
    intro hw0mem
    exact hwU (s16c34_uniqueMax_cent_of_mem_v0 D S.h61 h.hyp16 h3 h3rank hw0mem hw1)
  refine ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩), ?_, ?_, ?_⟩
  · exact (mem_preTil_iff_of_mem V₀ V hV (wTil V₀ V hV L) hwV).1 (by simpa [wSub] using hwW)
  · intro h1
    have hmem : w ∈ V₀ := by
      have h2 := (mkTil_eq_iff V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) 1).1 (by simpa using h1)
      have h3 : (IntMod.mk hV ⟨w, hwV⟩).val = w := rfl
      rw [h3] at h2
      simpa using h2
    exact hw0 hmem
  · intro R hRM hR hfix
    by_contra hle
    have hMs : D.M ≤ stabTil V₀ V :=
      le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
        h.hyp151.hyp125.pairFacts.le_normalizer₀
    have hR3 : IsPGroup 3 R := CFSG.Open.IsElemAbelian.isPGroup hR
    obtain ⟨n, hn⟩ := hR3.exists_card_eq
    rw [hn] at hle
    have h3n : 3 < 3 ^ n := not_le.1 hle
    have hn2 : 2 ≤ n := by
      have h1 : (3 : ℕ) ^ 1 < 3 ^ n := by simpa using h3n
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (3 : ℕ))).1 h1
      omega
    have hP : 3 ^ 2 ≤ Nat.card ↥R := by
      rw [hn]
      exact Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hn2
    obtain ⟨R', hR'le, hR'p, hR'c⟩ :=
      s16h_exists_noncyclic_le_preBarSub (M := D.M) hV hMs Nat.prime_three R hRM hR hP
    have hfixV : mkTil V₀ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈ fixV R := by
      rw [mem_fixV]
      exact hfix
    have hR'cElt : R' ≤ F11.CElt D.M V₀ w := by
      have h := s16c34_preBarSub_le_cElt (M := D.M) hV hfixV
      exact hR'le.trans h
    exact hwU
      (s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16 h3 hR'p hR'c hwV hw0 hR'cElt)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
