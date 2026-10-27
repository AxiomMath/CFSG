module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13Unitary
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13UnitaryDvdGen
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24Unitary
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24Sp
public import CFSG.LocalAnalysis.StandardType.GGStdPosC24SlNs
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13OrthEven
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13OrthSigned

public section

namespace CFSG.StandardType

open CFSG CFSG.StandardType CFSG.Assembly

theorem nbrC_not_dvd_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 := by
  intro h
  have h2 : p ∣ 2 ^ 2 := by simpa using h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))

theorem ggNbrTableBWeylNonSplitOn_unitary :
    GGNbrTableBWeylNonSplitOn GGNbrNonSplitUnitaryLabel := by
  rintro p hp hp2 ⟨tag, rank, n⟩ hlab ⟨hcase, hpq⟩ - Q hQ
  have hn : 1 ≤ n := hlab.1
  simp only at hcase hpq
  rcases hcase with ⟨ht, hr, h53⟩ | ⟨ht, hr⟩
  · subst ht
    have hr' : 3 ≤ rank := hr
    by_cases hpd : p ∣ rank + 1
    · have h4 : rank + 1 ≠ 4 := fun h => nbrC_not_dvd_four hp hp2 (h ▸ hpd)
      have hnd : ¬ (rank + 1 = 6 ∧ p = 3) := fun ⟨h6, h3⟩ => h53 ⟨by omega, h3⟩
      obtain ⟨K, _, _, hK, hQ', hl, hw⟩ :=
        recipeUnitary_dvd_reflGenW hp hpq hn (by omega) hpd hnd hQ
      exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => ⟨_, hl, hw⟩⟩
    · have hdq : (rank + 1, 2 ^ n) ≠ (3, 2) := fun h => by
        have := congrArg Prod.fst h
        simp only at this
        omega
      obtain ⟨K, _, _, hK, hQ', hP⟩ :=
        recipeUnitary_reflGenW hp hpq hn (by omega) hdq hpd hQ
      exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => hP⟩
  · subst ht
    have hr' : rank = 3 := hr
    subst hr'
    have hdq : ((4 : ℕ), 2 ^ n) ≠ (3, 2) := fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega
    obtain ⟨K, _, _, hK, hQ', hP⟩ :=
      recipeUnitary_reflGenW (d := 4) hp hpq hn (by omega) hdq (nbrC_not_dvd_four hp hp2) hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => hP⟩

theorem nbrC_labelAll_guard {lab : LargeEvenLabel} {P : LargeEvenRawCont}
    (h : LargeEvenLabelAll lab P) : LargeEvenLabelAll lab (LargeEvenSimpleGuard P) :=
  fun Q hQ => largeEvenRawDatum_mono (fun _ _ _ _ ⟨hq, hP⟩ => ⟨hq, fun _ _ => hP⟩) (h Q hQ)

theorem nbrC_rawDatum_guard {lab : LargeEvenLabel} {Q P : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab fun R _ I F => Q R I F ∧ P R I F) :
    LargeEvenRawDatum lab fun R _ I F => Q R I F ∧ LargeEvenSimpleGuard P R I F :=
  largeEvenRawDatum_mono (fun _ _ _ _ ⟨hq, hP⟩ => ⟨hq, fun _ _ => hP⟩) h

theorem ggNbrTableBWeylNonSplitOn_unitaryHyp :
    GGNbrTableBWeylNonSplitOn GGNbrNonSplitUnitaryHypLabel :=
  fun _ hp _ _ hlab h _ => nbrC_labelAll_guard (largeEvenLabelAll_reflGenW_unitaryHyp hp hlab h)

theorem ggNbrTableBWeylNonSplitOn_orth :
    GGNbrTableBWeylNonSplitOn GGNbrNonSplitOrthLabel := by
  rintro p hp hp2 ⟨tag, rank, n⟩ hlab hS - Q hQ
  have hn : 1 ≤ n := hlab.1
  apply nbrC_rawDatum_guard
  rcases hS with ⟨ht, hr, hpd⟩ | ⟨ht, hr, hpd⟩
  · simp only at ht hr hpd
    subst ht
    have h3 : rank ≠ 3 := by omega
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg h3] at hQ ⊢
    rcases Nat.even_or_odd rank with he | ho
    · exact recipeOmegaPlus_evenReflGenW hp hn hpd he hr hQ
    · have h5 : 5 ≤ rank := by
        obtain ⟨k, hk⟩ := ho
        omega
      exact recipeOmegaPlus_signedReflGenW hp hn hpd ho h5 hQ
  · simp only at ht hr hpd
    subst ht
    have h2 : rank ≠ 2 := by omega
    have h3 : rank ≠ 3 := by omega
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg h2, if_neg h3] at hQ ⊢
    rcases hpd with hpd | hpd
    · rcases Nat.even_or_odd (rank - 1) with he | ho
      · have h4 : 4 ≤ rank - 1 := by
          obtain ⟨k, hk⟩ := he
          omega
        exact recipeOmegaMinus_evenReflGenW hp hn hpd he h4 hQ
      · exact recipeOmegaMinus_signedReflGenW hp hn (Or.inr ⟨ho, hpd⟩) (by omega) hQ
    · exact recipeOmegaMinus_signedReflGenW hp hn (Or.inl hpd) (by omega) hQ

theorem ggNbrTableBWeylNonSplitOn_sympLin :
    GGNbrTableBWeylNonSplitOn GGNbrNonSplitSympLinLabel := by
  rintro p hp hp2 lab hlab hS -
  apply nbrC_labelAll_guard
  rcases hS with ⟨ht, -, hpd⟩ | ⟨ht, -, hn, rfl⟩ | ⟨ht, -, hn, rfl⟩
  · exact largeEvenLabelAll_reflGenW_spNonsplit hp hlab ⟨ht, hpd⟩
  · exact largeEvenLabelAll_reflGenW_linearNs hp hlab ⟨ht, by rw [hn]; norm_num⟩
  · exact largeEvenLabelAll_reflGenW_linearNs hp hlab ⟨ht, by rw [hn]; norm_num⟩

end CFSG.StandardType
