module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63Norm
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63Delta
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRule
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def UnitDvd63Q2Input : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 →
    GGStdSubTwoTorusNormSmallR 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
          (LargeEvenGUSet (Fin 6) K (2 ^ 1))) ∧
      GGStdSubTwoTorusDeltaSmall 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
          (LargeEvenGUSet (Fin 6) K (2 ^ 1)))

theorem unitDvd63_conjuncts {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hα : GGStdSubTwoTorusNormSmallR 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))))
    (hδ : GGStdSubTwoTorusDeltaSmall 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n)))) :
    GGOutdiagOdd 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) ∧
    ∃ r, GGTorusLift 3 r (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))) ∧
      GGStdSubTwoTorusNormSmallR 3 r (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
          (LargeEvenGUSet (Fin 6) K (2 ^ n))) ∧
      GGStdSubTwoTorusDeltaSmall 3 r (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
          (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hq : ¬ ((6 : ℕ) = 3 ∧ 2 ^ n = 2) := fun h => absurd h.1 (by norm_num)
  have hp : Nat.Prime 3 := Nat.prime_three
  have hrank : ggUnitaryTorusRank 3 6 = 3 := by
    simp [ggUnitaryTorusRank]
  have hlift := ggTorusLift_unitary hK hn (by norm_num) hdq hp hpq
  rw [hrank] at hlift
  exact ⟨InndiagSU.ggOutdiagOdd_unitary hK hn (by norm_num) hq 3, 3, hlift, hα, hδ⟩

theorem largeEvenLabelAll_stdSubSmallR_unitDvd63_two_le
    {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hl : GGUnitDvd63Label p lab) (hn2 : 2 ≤ lab.n) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmallR p r R I ∧ GGStdSubTwoTorusDeltaSmall p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := hl
  dsimp only at ht hl5 hn2
  subst ht hl5 hp3
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hn : 1 ≤ n := by omega
  exact ⟨K, i1, i2, hK, hQ', unitDvd63_conjuncts hK hn hpn
    (SmallU.ggStdSubTwoTorusNormSmallR_unitDvd63 hK hn2 hpn)
    (SmallU.ggStdSubTwoTorusDeltaSmall_unitDvd63 hK hn2 hpn)⟩

theorem largeEvenLabelAll_stdSubSmallR_unitDvd63_q2
    {p : ℕ} {lab : LargeEvenLabel}
    (hq2 : UnitDvd63Q2Input) (hl : GGUnitDvd63Label p lab) (hn1 : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmallR p r R I ∧ GGStdSubTwoTorusDeltaSmall p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := hl
  dsimp only at ht hl5 hn1
  subst ht hl5 hp3 hn1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, hQ', unitDvd63_conjuncts hK (le_refl 1) hpn
    (hq2 K hK).1 (hq2 K hK).2⟩

theorem largeEvenLabelAll_stdSubSmallR_unitDvd63
    {p : ℕ} {lab : LargeEvenLabel}
    (hq2 : UnitDvd63Q2Input) (hlab : LargeEvenInLambda2 lab) (hl : GGUnitDvd63Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmallR p r R I ∧ GGStdSubTwoTorusDeltaSmall p r R I := by
  by_cases h1 : lab.n = 1
  · exact largeEvenLabelAll_stdSubSmallR_unitDvd63_q2 hq2 hl h1
  · exact largeEvenLabelAll_stdSubSmallR_unitDvd63_two_le hlab hl
      (by have := hlab.1; omega)

theorem ggStdSubSmallInputOn_unitDvd63_two_le :
    GGStdSubSmallInputOn fun p lab => GGUnitDvd63Label p lab ∧ 2 ≤ lab.n :=
  ggStdSubSmallInputOn_of_labels_normSmallR ggLNoncyclicInput_holds fun _ _ _ hlab hS _ =>
    largeEvenLabelAll_stdSubSmallR_unitDvd63_two_le hlab hS.1 hS.2

theorem ggStdSubSmallInputOn_unitDvd63_of_q2
    (hq2 : UnitDvd63Q2Input) :
    GGStdSubSmallInputOn GGUnitDvd63Label :=
  ggStdSubSmallInputOn_of_labels_normSmallR ggLNoncyclicInput_holds fun _ _ _ hlab hS _ =>
    largeEvenLabelAll_stdSubSmallR_unitDvd63 hq2 hlab hS

theorem ggStdSubSmallInputOn_of_not_unitDvd63
    (hq2 : UnitDvd63Q2Input)
    {T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubSmallInputOn fun p lab => T p lab ∧ ¬ GGUnitDvd63Label p lab) :
    GGStdSubSmallInputOn T :=
  ((ggStdSubSmallInputOn_unitDvd63_of_q2 hq2).or h).mono fun p lab hT => by
    by_cases hl : GGUnitDvd63Label p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hT, hl⟩

end CFSG.StandardType

end
