module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGEndNodeAdmUnitaryDvdInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
    GGTableBUnitaryLiftLabel p lab → p ∣ lab.rank + 1 → 4 ≤ lab.rank →
      LargeEvenLabelAll lab fun R _ I _ => GGEndNodeAdm p (ggUnitaryTorusRank p (lab.rank + 1)) R I

@[expose] def GGEndNodeAdmUnitarySmallInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
    GGTableBUnitaryLiftLabel p lab → lab.n = 1 → (lab.rank = 3 ∨ lab.rank = 4) →
      LargeEvenLabelAll lab fun R _ I _ => GGEndNodeAdm p (ggUnitaryTorusRank p (lab.rank + 1)) R I

theorem largeEvenLabelAll_endNodeAdm_unitary {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hl : GGTableBUnitaryLiftLabel p lab)
    (hpd : ¬ p ∣ lab.rank + 1) (hs : ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 4))) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGEndNodeAdm p (ggUnitaryTorusRank p (lab.rank + 1)) R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpq⟩ := hl
  dsimp only at htag hpq hpd hs ⊢
  have hn : 1 ≤ n := hlab.1
  have hr : ggUnitaryTorusRank p (l + 1) = l + 1 - 2 := by
    simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
  rw [hr]
  rcases htag with rfl | ⟨rfl, rfl⟩
  · obtain ⟨-, hl2, hl22⟩ := hlab
    dsimp only at hl2 hl22
    have hq : 2 < 2 ^ n ∨ 6 ≤ l + 1 := by
      by_cases hn1 : n = 1
      · subst hn1
        right
        have : l ≠ 2 := fun h => by have := hl22 h; omega
        omega
      · left
        have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
    exact ⟨K, i1, i2, hK, hq', TableBUE.ggEndNodeAdm_unitary
      (TableBU.unitaryFieldData_of_card hK hn) hK (by omega) hp hpq hpd hq⟩
  · have hq : 2 < 2 ^ n ∨ 6 ≤ 3 + 1 := by
      left
      have hn1 : n ≠ 1 := fun h => hs ⟨h, Or.inl rfl⟩
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [↓reduceIte] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
    exact ⟨K, i1, i2, hK, hq', TableBUE.ggEndNodeAdm_unitary
      (TableBU.unitaryFieldData_of_card hK hn) hK (by norm_num) hp hpq hpd hq⟩

theorem largeEvenLabelAll_endNodeAdm_unitary_three {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hl : GGTableBUnitaryLiftLabel p lab) (hl2 : lab.rank = 2) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGEndNodeAdm p (ggUnitaryTorusRank p (lab.rank + 1)) R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpq⟩ := hl
  dsimp only at htag hpq hl2 ⊢
  subst hl2
  rcases htag with rfl | ⟨-, h3⟩
  · obtain ⟨hn, -, hl22⟩ := hlab
    dsimp only at hn hl22
    have h2 : 2 < 2 ^ n := by
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (hl22 rfl)
      omega
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
    exact ⟨K, i1, i2, hK, hq', TableBUE.ggEndNodeAdm_unitary_three
      (TableBU.unitaryFieldData_of_card hK hn) hK h2 hp hpq _⟩
  · exact absurd h3 (by norm_num)

theorem ggEndNodeAdmUnitaryInput_of_parts (hdvd : GGEndNodeAdmUnitaryDvdInput)
    (hsmall : GGEndNodeAdmUnitarySmallInput) : GGEndNodeAdmUnitaryInput := by
  intro p lab hp hlab hl
  by_cases hpd : p ∣ lab.rank + 1
  · by_cases hl2 : lab.rank = 2
    · exact largeEvenLabelAll_endNodeAdm_unitary_three hp hlab hl hl2
    · refine hdvd p lab hp hlab hl hpd ?_
      have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hlab.1 hl.2
      have hr2 : 2 ≤ lab.rank := by
        rcases hl.1 with ht | ⟨-, ht⟩
        · have := hlab.2
          rw [ht] at this
          exact this.1
        · omega
      by_contra h4
      have h3 : lab.rank = 3 := by omega
      rw [h3] at hpd
      have hp4 : p ∣ 2 ^ 2 := by simpa using hpd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hp4))
  by_cases hs : lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 4)
  · exact hsmall p lab hp hlab hl hs.1 hs.2
  · exact largeEvenLabelAll_endNodeAdm_unitary hp hlab hl hpd hs

end CFSG.StandardType
