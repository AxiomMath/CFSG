module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestVac
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeTableB
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperUnitaryLabel
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSp

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGStdSubFixedJOn_of_labels_norm (ha₀ : GGLNoncyclicInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
        ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusNorm p r R I ∧ GGStdSubTwoTorusDelta p r R I) :
    GGStdSubFixedJOn S := by
  intro G _ _ p B Bs x L D J hcfg hM
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab ∧ LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs.1 hs.2) (fun _ _ _ _ _ _ hP => ⟨hP.1, hP.2.1⟩) hM
  obtain ⟨hle, hI2⟩ := ggStdSubInputs_of_twoTorusNorm ha₀ hcfg
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩) hM')
  exact ⟨GGStdSubFixedJ_eq_of_le hcfg hle, hI2⟩

@[expose] def GGStdSubSmallUnitaryLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBUnitaryLiftLabel p lab ∧ ¬ p ∣ lab.rank + 1 ∧ (2 ≤ lab.n ∨ lab.rank ≤ 3)

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag in
theorem stdSubNorm_unitary_recipe {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hq : 2 ≤ n ∨ d ≤ 4) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) :
    GGOutdiagOdd p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) ∧
      GGStdSubTwoTorusNorm p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) ∧
      GGStdSubTwoTorusDelta p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have h := TableBU.unitaryFieldData_of_card hK hn
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hZ := StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd
  refine ⟨ggOutdiagOdd_of_prime fun φ hφ hφp =>
      TableBUE.mem_range_conj_of_pow_eq_one h hK hd hdq hp hpq hpd hφ hφp, ?_⟩
  rcases hq with hn2 | hd4
  · exact StdSubRestU.ggStdSubTwoTorusNorm_unitary h hK hn2 hp hpq hpd hd hZ
  · exact StdSubRestU.ggStdSubTwoTorusNorm_unitary_of_le_four h hK hp hpq hpd hd hd4 hdq hZ

theorem largeEvenLabelAll_stdSubNorm_unitary {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hl : GGStdSubSmallUnitaryLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNorm p r R I ∧ GGStdSubTwoTorusDelta p r R I := by
  obtain ⟨hU, hpd, hn⟩ := hl
  have hr : ggUnitaryTorusRank p (lab.rank + 1) = lab.rank + 1 - 2 := by
    simp only [ggUnitaryTorusRank, hpd, ↓reduceIte]
  have hmain : LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧
      GGStdSubTwoTorusNorm p (lab.rank + 1 - 2) R I ∧
        GGStdSubTwoTorusDelta p (lab.rank + 1 - 2) R I := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨htag, hpq⟩ := hU
    dsimp only at htag hpq hpd hn ⊢
    intro Q hQ
    have hn1 : 1 ≤ n := hlab.1
    have hq' : 2 ≤ n ∨ l + 1 ≤ 4 := hn.imp id fun h' => by omega
    rcases htag with ht | ⟨ht, hl3⟩
    · subst ht
      have hl2 : 2 ≤ l := hlab.2.1
      have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
        intro he
        have h1 : l + 1 = 3 := congrArg Prod.fst he
        have h2 : 2 ^ n = 2 := congrArg Prod.snd he
        have h3 : 2 ≤ n := hlab.2.2 (show l = 2 by omega)
        have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
        omega
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      obtain ⟨K, i1, i2, hK, hq⟩ := hQ
      exact ⟨K, i1, i2, hK, hq,
        stdSubNorm_unitary_recipe hK hn1 hq' (by omega) hdq hp hpq hpd⟩
    · subst ht hl3
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      simp only [↓reduceIte] at hQ ⊢
      obtain ⟨K, i1, i2, hK, hq⟩ := hQ
      exact ⟨K, i1, i2, hK, hq, stdSubNorm_unitary_recipe hK hn1 hq' (by norm_num)
        (fun he => absurd (congrArg Prod.fst he) (by norm_num)) hp hpq hpd⟩
  exact ((largeEvenLabelAll_torusLift_unitaryLift hp hlab hU).and hmain).mono
    fun _ _ _ _ hh => ⟨hh.2.1, lab.rank + 1 - 2, hr ▸ hh.1, hh.2.2⟩

theorem GGStdSubFixedJOn_unitary_of_noncyclic (ha₀ : GGLNoncyclicInput) :
    GGStdSubFixedJOn GGStdSubSmallUnitaryLabel :=
  GGStdSubFixedJOn_of_labels_norm ha₀ fun _ _ hp hlab hS _ =>
    largeEvenLabelAll_stdSubNorm_unitary hp hlab hS

theorem largeEvenLabelAll_centerPrime_unitary {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (hU : GGTableBUnitaryLiftLabel p lab)
    (hpd : ¬ p ∣ lab.rank + 1) : LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpq⟩ := hU
  dsimp only at htag hpq hpd ⊢
  have hn1 : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn1 hpq
  intro Q hQ
  rcases htag with ht | ⟨ht, hl3⟩
  · subst ht
    have hl2 : 2 ≤ l := hlab.2.1
    have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
      intro he
      have h1 : l + 1 = 3 := congrArg Prod.fst he
      have h2 : 2 ^ n = 2 := congrArg Prod.snd he
      have h3 : 2 ≤ n := hlab.2.2 (show l = 2 by omega)
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      omega
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, StdSubRestU.ggCenterPrime_unitary hK hn1 (by omega) hdq hp hp2 hpd⟩
  · subst ht hl3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [↓reduceIte] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, StdSubRestU.ggCenterPrime_unitary hK hn1 (by norm_num)
      (fun he => absurd (congrArg Prod.fst he) (by norm_num)) hp hp2 hpd⟩

theorem ggStdSubIOneProperInputOn_unitary_holds (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGIOneUnitaryLabel :=
  ggStdSubIOneProperInputOn_unitary ha₀ fun _ _ hp hlab hl =>
    largeEvenLabelAll_centerPrime_unitary hp hlab ⟨Or.inl hl.1, hl.2.1⟩ hl.2.2.1

theorem ggStdSubSmallInputOn_unitary (ha₀ : GGLNoncyclicInput) :
    GGStdSubSmallInputOn GGStdSubSmallUnitaryLabel :=
  GGStdSubSmallInputOn_of_fixedJ (GGStdSubFixedJOn_unitary_of_noncyclic ha₀)

theorem GGStdSubFixedJOn_unitary :
    GGStdSubFixedJOn GGStdSubSmallUnitaryLabel :=
  GGStdSubFixedJOn_unitary_of_noncyclic ggLNoncyclicInput_holds

end Unitary

theorem GGStdSubSmallInputOn.mono {S T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubSmallInputOn T) (hST : ∀ p lab, S p lab → T p lab) : GGStdSubSmallInputOn S :=
  fun G _ _ p B Bs x L D J hcfg hM hsm => h G p B Bs x L D J hcfg
    (largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hST p lab hP.1, hP.2⟩) hM) hsm

@[expose] def GGStdSubSmallRest2Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGStdSubSmallRestLabel p lab ∧ ¬ GGStdSubSmallVacLabel p lab ∧ ¬ GGStdSubSmallUnitaryLabel p lab

theorem ggStdSubSmallInputOn_rest_of_rest2
    (h : GGStdSubSmallInputOn GGStdSubSmallRest2Label) :
    GGStdSubSmallInputOn GGStdSubSmallRestLabel :=
  ((ggStdSubSmallInputOn_vac.or (ggStdSubSmallInputOn_unitary ggLNoncyclicInput_holds)).or
    h).mono fun p lab hR => by
      by_cases h1 : GGStdSubSmallVacLabel p lab
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : GGStdSubSmallUnitaryLabel p lab
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨hR, h1, h2⟩

theorem GGStdSubFixedJOn_symplectic :
    GGStdSubFixedJOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1 :=
  GGStdSubFixedJOn_symplectic_of_sp ggStdSubTwoTorus_symplectic_of_card

theorem GGStdSubFixedJOn_sectors :
    GGStdSubFixedJOn fun p lab => (GGTypeASplitLabel p lab ∨
        ((lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1)) ∨
      GGStdSubSmallUnitaryLabel p lab :=
  (GGStdSubFixedJOn_typeA_split.or GGStdSubFixedJOn_symplectic).or GGStdSubFixedJOn_unitary

end CFSG.StandardType
