module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThree
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeSmall
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Unitary


open CFSG.ClassicalGroups.UnitaryFlag in
theorem stdSubNormSmall_unitary_two_recipe {K : Type} [Field K] [Finite K] {d : ℕ}
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hd3 : ¬ 3 ∣ d) (hd5 : 5 ≤ d) :
    GGOutdiagOdd 3 (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
          (LargeEvenGUSet (Fin d) K (2 ^ 1))) ∧
      GGStdSubTwoTorusNormSmall 3 (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
          (LargeEvenGUSet (Fin d) K (2 ^ 1))) ∧
      GGStdSubTwoTorusDeltaSmall 3 (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
          (LargeEvenGUSet (Fin d) K (2 ^ 1))) := by
  have h := TableBU.unitaryFieldData_of_card hK (le_refl 1)
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hd : 3 ≤ d := by omega
  have hdq : (d, 2 ^ 1) ≠ (3, 2) := by
    intro he
    have h1 := congrArg Prod.fst he
    simp only at h1
    omega
  have hZ := StdSubRestU.ggCenterPrime_unitary hK (le_refl 1) hd hdq hp (by norm_num) hd3
  have hO : GGOutdiagPrime 3 (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
        (LargeEvenGUSet (Fin d) K (2 ^ 1))) := fun φ hφ hφp =>
    TableBUE.mem_range_conj_of_pow_eq_one h hK hd hdq hp hpq hd3 hφ hφp
  exact ⟨ggOutdiagOdd_of_prime hO,
    ggStdSubTwoTorusNormSmall_of_elt hp hO (TableBUE.center_proj_eq_bot hK hd hdq) hZ
      (StdSubRestThreeU.ggStdSubTwoTorusEltNormSmall_unitary_two h hK hd3 hd5),
    ggStdSubTwoTorusDeltaSmall_of_delta (ggStdSubTwoTorusDelta_of_prime hO hZ)⟩

@[expose] def GGStdSubSmallUnitaryTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.n = 1 ∧ p = 3 ∧ ¬ 3 ∣ lab.rank + 1 ∧ 4 ≤ lab.rank

theorem largeEvenLabelAll_stdSubNormSmall_unitaryTwo {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hlab : LargeEvenInLambda2 lab) (hl : GGStdSubSmallUnitaryTwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmall p r R I ∧ GGStdSubTwoTorusDeltaSmall p r R I := by
  obtain ⟨ht, hn, hp3, hd3, hl5⟩ := hl
  have hU : GGTableBUnitaryLiftLabel p lab := ⟨Or.inl ht, by rw [hn, hp3]; norm_num⟩
  have hr : ggUnitaryTorusRank p (lab.rank + 1) = lab.rank + 1 - 2 := by
    simp only [ggUnitaryTorusRank, hp3, hd3, ↓reduceIte]
  have hmain : LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      GGStdSubTwoTorusNormSmall p (lab.rank + 1 - 2) R I ∧
        GGStdSubTwoTorusDeltaSmall p (lab.rank + 1 - 2) R I := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hn hd3 hl5 ⊢
    subst ht hn hp3
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, stdSubNormSmall_unitary_two_recipe hK hd3 (by omega)⟩
  exact ((largeEvenLabelAll_torusLift_unitaryLift hp hlab hU).and hmain).mono
    fun _ _ _ _ hh => ⟨hh.2.1, lab.rank + 1 - 2, hr ▸ hh.1, hh.2.2⟩

end Unitary

theorem ggStdSubSmallInputOn_unitaryTwo :
    GGStdSubSmallInputOn GGStdSubSmallUnitaryTwoLabel :=
  ggStdSubSmallInputOn_of_labels_normSmall ggLNoncyclicInput_holds fun _ _ hp hlab hS _ =>
    largeEvenLabelAll_stdSubNormSmall_unitaryTwo hp hlab hS

@[expose] def GGStdSubSmallRest4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGStdSubSmallRest3Label p lab ∧ ¬ GGStdSubSmallUnitaryTwoLabel p lab

theorem ggStdSubSmallInputOn_rest2_of_rest4
    (hF3 : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGStdSubSmallInputOn GGStdSubSmallRest4Label) :
    GGStdSubSmallInputOn GGStdSubSmallRest2Label :=
  ggStdSubSmallInputOn_rest2_of_rest3 hF3 ((ggStdSubSmallInputOn_unitaryTwo.or h).mono
    fun p lab hR => by
      by_cases h1 : GGStdSubSmallUnitaryTwoLabel p lab
      · exact Or.inl h1
      · exact Or.inr ⟨hR, h1⟩)

theorem ggStdSubSmallRest4Label_cases {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGStdSubSmallRest4Label p lab)
    (hs : LargeEvenSplit p lab) :
    (lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ 3 ≤ lab.rank ∧ p ∣ lab.rank + 1) ∨
      (p = 3 ∧ lab.n = 1 ∧ ((lab.tag = .A ∧ 5 ≤ lab.rank) ∨
        ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank))) ∨
      ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∨
      lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6 := by
  rcases ggStdSubSmallRest3Label_cases hp hlab h.1 hs with
    ⟨ht, hpq, hl3, hd | ⟨hn, hl4⟩⟩ | h2 | h2
  · exact Or.inl ⟨ht, hpq, hl3, hd⟩
  · by_cases hd : p ∣ lab.rank + 1
    · exact Or.inl ⟨ht, hpq, hl3, hd⟩
    · have hp3 : p = 3 := by
        rw [hn] at hpq
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa using hpq)
      exact absurd ⟨ht, hn, hp3, hp3 ▸ hd, hl4⟩ h.2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h2)

end CFSG.StandardType
