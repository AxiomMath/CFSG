module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213CharY
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Cover857
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213CoverExc
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213RestNN4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2

public section
namespace CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def Rest15Models (M L : Subgroup G) : Prop :=
  (∃ p, ∃ f ≤ 2, LieModel (BarInf L) .G2 0 p f ∧ (p = 3 ∨ 3 ≤ Open.pRank 3 M)) ∨
  (∃ p f, (p ≠ 2 ∨ f ≤ 2) ∧ LieModel (BarInf L) .trialityD4 0 p f) ∨
  LieModel (BarInf L) .PSL 3 2 2 ∨ LieModel (BarInf L) .PSU 3 2 3 ∨
  ((IsSpor (BarInf L) .M12 ∨ IsSpor (BarInf L) .M24 ∨ IsSpor (BarInf L) .Ru ∨
    IsSpor (BarInf L) .J4) ∧ 3 ≤ Open.pRank 3 M)

theorem rest15_models_of_rank_three {M L : Subgroup G} {t : StatedLieTag} {p f : ℕ}
    (hres : S21_3Closed2 L ∨ S21_3ClosedL2 L ∨ S21_3ClosedTorusL3 L ∨ S21_3ClosedU3 L ∨
      S21_3ClosedChar M L ∨ S21_3ClosedSmall M L ∨
      (t = .PSL ∧ p = 2 ∧ f = 2) ∨ (t = .PSU ∧ p = 2 ∧ f = 3) ∨
      (p ≠ 2 ∧ f = 1 ∧ 3 ≤ Open.pRank p M))
    (hC2 : ¬ S21_3Closed2 L) (hL2 : ¬ S21_3ClosedL2 L) (hTL : ¬ S21_3ClosedTorusL3 L)
    (hU3 : ¬ S21_3ClosedU3 L) (hCh : ¬ S21_3ClosedChar M L) (hSmall : ¬ S21_3ClosedSmall M L)
    (hY : ¬ S21_3ClosedCharY M L) (ht : t = .PSL ∨ t = .PSU)
    (hX : LieModel (BarInf L) t 3 p f) :
    LieModel (BarInf L) .PSL 3 2 2 ∨ LieModel (BarInf L) .PSU 3 2 3 := by
  rcases hres with h | h | h | h | h | h | h | h | h
  · exact absurd h hC2
  · exact absurd h hL2
  · exact absurd h hTL
  · exact absurd h hU3
  · exact absurd h hCh
  · exact absurd h hSmall
  · obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl hX
  · obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inr hX
  · obtain ⟨hp2, rfl, hM⟩ := h
    have hmodel : LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1 := by
      rcases ht with rfl | rfl
      · exact Or.inl hX
      · exact Or.inr hX
    exact absurd ⟨p, hp2, hmodel, hM⟩ hY

omit [Finite G] in
private theorem closedTorus_of_twistedF4 {L : Subgroup G} {f : ℕ}
    (hX : LieModel (BarInf L) .twistedF4 0 2 f) : S21_3ClosedTorus L := by
  have hf3 : 3 ≤ f := hX.admissible.2.2.2.2.2
  have hf2 : 2 ≤ f := by omega
  by_cases h6 : f = 6
  · subst h6
    refine Or.inr ⟨7, 2, 6, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    exact Or.inr (Or.inr ⟨rfl, hX⟩)
  · obtain ⟨r, hr, hrd, hprim⟩ :=
      CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one f hf2 h6
    have hpp : CFSG.Timmesfeld.IsPrimitivePrimeDivisor r f := ⟨hr, hrd, hprim⟩
    have hfr : f < r := uc22p22i_lt_of_primitive hpp (by omega)
    have hr2 : r ≠ 2 := hpp.ne_two (by omega)
    have hr3 : r ≠ 3 := by
      intro h3
      have := hpp.eq_two_of_dvd_three (by omega) (by rw [h3])
      omega
    have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
    refine Or.inr ⟨r, 2, f, hr, hr5, hrd, fun hrf => ?_, Or.inr (Or.inr ⟨rfl, hX⟩)⟩
    exact absurd (Nat.le_of_dvd (by omega : 0 < f) hrf) (not_le.mpr hfr)

private theorem list857_lie_absurd {M L : Subgroup G} (hGA : GriessAllModelsStatement)
    (hL : L ∈ calC M) (h3 : Open.pRank 3 L ≤ 2)
    (h : (∃ p f, p ^ f % 3 = 2 ∧ LieModel (BarInf L) .PSL 4 p f) ∨
      (∃ p f, p ^ f % 3 = 1 ∧ LieModel (BarInf L) .PSU 4 p f) ∨
      (∃ p f, p ^ f % 3 = 2 ∧
        (LieModel (BarInf L) .PSL 5 p f ∨
          UCK.ThreeCover (fun Y _ => LieModel Y .PSL 5 p f) (BarInf L))) ∨
      (∃ p f, p ^ f % 3 = 1 ∧
        (LieModel (BarInf L) .PSU 5 p f ∨
          UCK.ThreeCover (fun Y _ => LieModel Y .PSU 5 p f) (BarInf L))) ∨
      (∃ p f, LieModel (BarInf L) .PSp 2 p f))
    (hCZ : ¬ S21_3ClosedZ L) (hC2 : ¬ S21_3Closed2 L)
    (hT4 : ¬ S21_3ClosedTorus4 L) (hCh : ¬ S21_3ClosedChar M L)
    (hU54 : ¬ S21_3ClosedU54 L) : False := by
  rcases uc22s213_closed_of_list857_lie hGA hL h3 h with h | h | h | h | h
  · exact hCZ h
  · exact hC2 h
  · exact hT4 h
  · exact hCh h
  · exact hU54 h

private theorem list857_one_absurd {M L : Subgroup G} (hGA : GriessAllModelsStatement)
    (hL : L ∈ calC M) (h3 : Open.pRank 3 L ≤ 2) (hZ3 : ¬ 3 ∣ Nat.card (center (Bar2 L)))
    (hC : ¬ S21_3Closed L) (hCZ : ¬ S21_3ClosedZ L) (hC2 : ¬ S21_3Closed2 L)
    (hT4 : ¬ S21_3ClosedTorus4 L) (hCh : ¬ S21_3ClosedChar M L)
    (hU54 : ¬ S21_3ClosedU54 L)
    (h : (∃ p f, p ^ f % 3 = 2 ∧ LieModel (BarInf L) .PSL 4 p f) ∨
      (∃ p f, p ^ f % 3 = 1 ∧ LieModel (BarInf L) .PSU 4 p f) ∨
      (∃ p f, p ^ f % 3 = 2 ∧
        (LieModel (BarInf L) .PSL 5 p f ∨
          UCK.ThreeCover (fun Y _ => LieModel Y .PSL 5 p f) (BarInf L))) ∨
      (∃ p f, p ^ f % 3 = 1 ∧
        (LieModel (BarInf L) .PSU 5 p f ∨
          UCK.ThreeCover (fun Y _ => LieModel Y .PSU 5 p f) (BarInf L))) ∨
      (∃ p f, LieModel (BarInf L) .PSp 2 p f) ∨
      IsSpor (BarInf L) .M11 ∨ IsSpor (BarInf L) .M22 ∨ IsSpor (BarInf L) .M23 ∨
      IsSpor (BarInf L) .HS ∨ IsAlt (BarInf L) 7 ∨ IsAlt (BarInf L) 6) : False := by
  rcases h with hL4 | hU4 | hL5 | hU5 | hPSp | hM11 | hM22 | hM23 | hHS | hA7 | hA6
  · exact list857_lie_absurd hGA hL h3 (Or.inl hL4) hCZ hC2 hT4 hCh hU54
  · exact list857_lie_absurd hGA hL h3 (Or.inr (Or.inl hU4)) hCZ hC2 hT4 hCh hU54
  · obtain ⟨p, f, hmod, hX | hcov⟩ := hL5
    · exact list857_lie_absurd hGA hL h3
        (Or.inr (Or.inr (Or.inl ⟨p, f, hmod, Or.inl hX⟩))) hCZ hC2 hT4 hCh hU54
    · exact absurd hcov (uc22s213_not_threeCover_barInf hL (fun Y _ => LieModel Y .PSL 5 p f))
  · obtain ⟨p, f, hmod, hX | hcov⟩ := hU5
    · exact list857_lie_absurd hGA hL h3
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hmod, Or.inl hX⟩)))) hCZ hC2 hT4 hCh hU54
    · exact absurd hcov (uc22s213_not_threeCover_barInf hL (fun Y _ => LieModel Y .PSU 5 p f))
  · exact list857_lie_absurd hGA hL h3
      (Or.inr (Or.inr (Or.inr (Or.inr hPSp)))) hCZ hC2 hT4 hCh hU54
  · exact hC ⟨hZ3, Or.inr (Or.inl hM11)⟩
  · exact hC ⟨hZ3, Or.inr (Or.inr (Or.inl hM22))⟩
  · exact hC ⟨hZ3, Or.inr (Or.inr (Or.inr (Or.inl hM23)))⟩
  · exact hC ⟨hZ3, Or.inr (Or.inr (Or.inr (Or.inr hHS)))⟩
  · exact hC ⟨hZ3, Or.inl ⟨7, by norm_num, hA7⟩⟩
  · exact hC ⟨hZ3, Or.inl ⟨6, by norm_num, hA6⟩⟩

omit [Finite G] in
private theorem closedZ_of_spor_J2 {L : Subgroup G} (h : IsSpor (BarInf L) .J2) :
    S21_3ClosedZ L := by
  unfold S21_3ClosedZ
  simp [h]

private theorem list857_two_absurd {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    (h : F08.IsA6Z3 (BarInf L) ∨ F08.IsA7Z3 (BarInf L) ∨ F08.IsM22Z3 (BarInf L)) : False := by
  have hZ := center_barInf_eq_bot hq
  rcases h with h | h | h
  · have := h.2.1
    rw [hZ, card_bot] at this
    norm_num at this
  · have := h.2.1
    rw [hZ, card_bot] at this
    norm_num at this
  · have := h.2.1
    rw [hZ, card_bot] at this
    norm_num at this

private theorem models_of_rank_three {M L : Subgroup G}
    (h : LieModel (BarInf L) .PSL 3 2 2 ∨ LieModel (BarInf L) .PSU 3 2 3) :
    Rest15Models M L := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

private theorem models_of_exceptional {M L : Subgroup G}
    (h : S21_3ClosedTorus L ∨ S21_3ClosedSmall M L ∨
      (∃ p, ∃ f ≤ 2, LieModel (BarInf L) .G2 0 p f ∧ (p = 3 ∨ 3 ≤ Open.pRank 3 M)) ∨
      (∃ p f, (p ≠ 2 ∨ f ≤ 2) ∧ LieModel (BarInf L) .trialityD4 0 p f))
    (hT : ¬ S21_3ClosedTorus L) (hSmall : ¬ S21_3ClosedSmall M L) :
    Rest15Models M L := by
  rcases h with h | h | h | h
  · exact absurd h hT
  · exact absurd h hSmall
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

private theorem models_of_spor {M L : Subgroup G}
    (h : IsSpor (BarInf L) .M12 ∨ IsSpor (BarInf L) .M24 ∨ IsSpor (BarInf L) .Ru ∨
      IsSpor (BarInf L) .J4) (h3M : 3 ≤ Open.pRank 3 M) : Rest15Models M L :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨h, h3M⟩)))

omit [Finite G] in
private theorem closedZ_of_spor_He {L : Subgroup G} (h : IsSpor (BarInf L) .He) :
    S21_3ClosedZ L := by
  unfold S21_3ClosedZ
  simp [h]

theorem rest15_coverage {M L : Subgroup G} (hGA : GriessAllModelsStatement)
    (hL : L ∈ calC M) (hC : ¬ S21_3Closed L) (hC2 : ¬ S21_3Closed2 L)
    (hCZ : ¬ S21_3ClosedZ L) (hSp : ¬ S21_3ClosedSpor M L)
    (hL2 : ¬ S21_3ClosedL2 L) (hT : ¬ S21_3ClosedTorus L)
    (hSmall : ¬ S21_3ClosedSmall M L) (hlist : S21_3List L)
    (hU3 : ¬ S21_3ClosedU3 L) (hTL : ¬ S21_3ClosedTorusL3 L)
    (hT4 : ¬ S21_3ClosedTorus4 L) (hCh : ¬ S21_3ClosedChar M L)
    (hU54 : ¬ S21_3ClosedU54 L) (hY : ¬ S21_3ClosedCharY M L)
    (h3 : Open.pRank 3 L ≤ 2) :
    M ≤ normalizer (L : Set G) ∨ FiveCovers (Bar2 L) ∨
      3 ∣ Nat.card (center (Bar2 L)) ∨ Rest15Models M L := by
  by_cases hMN : M ≤ normalizer (L : Set G)
  · exact Or.inl hMN
  by_cases hFC : FiveCovers (Bar2 L)
  · exact Or.inr (Or.inl hFC)
  by_cases hZ : 3 ∣ Nat.card (center (Bar2 L))
  · exact Or.inr (Or.inr (Or.inl hZ))
  have hZ3 : ¬ 3 ∣ Nat.card (center (Bar2 L)) := hZ
  rcases hlist with hZ' | ⟨_, hrest⟩ | ⟨_, hrest1⟩
  · exact absurd hZ' hZ
  · rcases hrest with h857 | hSL3
    ·
      rcases h857 with h1 | h2 | h3list
      · exact (list857_one_absurd hGA hL h3 hZ3 hC hCZ hC2 hT4 hCh hU54 h1).elim
      · exact (list857_two_absurd hL.2.2 h2).elim
      · rcases h3list with hL33 | ⟨p, f, hG2⟩ | hU33 | ⟨p, f, hTri⟩ |
          ⟨f, h2F4⟩ | hTits | hJ2 | hHe | hRu | hJ4 | hM12 | hM24
        · by_cases h3M : 3 ≤ Open.pRank 3 M
          · exact absurd ⟨3, by norm_num, Or.inl hL33, h3M⟩ hY
          · exact absurd ⟨Or.inl hL33, by omega⟩ hSmall
        · exact Or.inr (Or.inr (Or.inr
            (models_of_exceptional (uc22s213_closed_of_exceptional (Or.inl ⟨p, f, hG2⟩))
              hT hSmall)))
        · by_cases h3M : 3 ≤ Open.pRank 3 M
          · exact absurd ⟨3, by norm_num, Or.inr hU33, h3M⟩ hY
          · exact absurd ⟨Or.inr (Or.inl hU33), by omega⟩ hSmall
        · exact Or.inr (Or.inr (Or.inr
            (models_of_exceptional
              (uc22s213_closed_of_exceptional (Or.inr (Or.inl ⟨p, f, hTri⟩))) hT hSmall)))
        · exact absurd (closedTorus_of_twistedF4 h2F4) hT
        · exact absurd (Or.inl hTits) hT
        · exact absurd (closedZ_of_spor_J2 hJ2) hCZ
        · exact absurd (closedZ_of_spor_He hHe) hCZ
        · by_cases h3M : 3 ≤ Open.pRank 3 M
          · exact Or.inr (Or.inr (Or.inr (models_of_spor (Or.inr (Or.inr (Or.inl hRu))) h3M)))
          · exact absurd ⟨Or.inr (Or.inr (Or.inl hRu)), by omega⟩ hSp
        · by_cases h3M : 3 ≤ Open.pRank 3 M
          · exact Or.inr (Or.inr (Or.inr (models_of_spor (Or.inr (Or.inr (Or.inr hJ4))) h3M)))
          · exact absurd ⟨Or.inr (Or.inr (Or.inr hJ4)), by omega⟩ hSp
        · by_cases h3M : 3 ≤ Open.pRank 3 M
          · exact Or.inr (Or.inr (Or.inr (models_of_spor (Or.inl hM12) h3M)))
          · exact absurd ⟨Or.inl hM12, by omega⟩ hSp
        · by_cases h3M : 3 ≤ Open.pRank 3 M
          · exact Or.inr (Or.inr (Or.inr (models_of_spor (Or.inr (Or.inl hM24)) h3M)))
          · exact absurd ⟨Or.inr (Or.inl hM24), by omega⟩ hSp
    ·
      rcases hSL3 with ⟨p, f, _, hX⟩ | ⟨p, f, _, hX⟩ | ⟨p, f, _, hcov⟩ | ⟨p, f, _, hcov⟩
      · exact Or.inr (Or.inr (Or.inr (models_of_rank_three (rest15_models_of_rank_three
          (uc22s213_closed_of_rank_three hGA hL (Or.inl rfl) hX)
          hC2 hL2 hTL hU3 hCh hSmall hY (Or.inl rfl) hX))))
      · exact Or.inr (Or.inr (Or.inr (models_of_rank_three (rest15_models_of_rank_three
          (uc22s213_closed_of_rank_three hGA hL (Or.inr rfl) hX)
          hC2 hL2 hTL hU3 hCh hSmall hY (Or.inr rfl) hX))))
      · exact absurd hcov (uc22s213_not_threeCover_barInf hL (fun Y _ => LieModel Y .PSL 3 p f))
      · exact absurd hcov (uc22s213_not_threeCover_barInf hL (fun Y _ => LieModel Y .PSU 3 p f))
  ·
    rcases hrest1 with ⟨p, f, _, hX⟩ | ⟨p, f, _, hX⟩
    · exact Or.inr (Or.inr (Or.inr (models_of_rank_three (rest15_models_of_rank_three
        (uc22s213_closed_of_rank_three hGA hL (Or.inl rfl) hX)
        hC2 hL2 hTL hU3 hCh hSmall hY (Or.inl rfl) hX))))
    · exact Or.inr (Or.inr (Or.inr (models_of_rank_three (rest15_models_of_rank_three
        (uc22s213_closed_of_rank_three hGA hL (Or.inr rfl) hX)
        hC2 hL2 hTL hU3 hCh hSmall hY (Or.inr rfl) hX))))

end CFSG.LocalAnalysis.UniquenessCase.UC22
end
