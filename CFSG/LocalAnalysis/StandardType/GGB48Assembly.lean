module

public import CFSG.LocalAnalysis.StandardType.GGB48SpGlue
public import CFSG.LocalAnalysis.StandardType.GGB48Labels
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylAutomizer
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrRowFilter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem ggB48_rows {labN : LargeEvenLabel} (h : GGTablePRow 3 ⟨.A, 2, 2⟩ labN) :
    labN = ⟨.A, 3, 2⟩ ∨ labN = ⟨.D, 3, 2⟩ ∨ labN = ⟨.C, 3, 2⟩ ∨ labN = ⟨.twD, 4, 2⟩ ∨
      labN = ⟨.A, 5, 1⟩ ∨ labN = ⟨.A, 6, 1⟩ := by
  have hc := ggTablePRow_typeA (p := 3) (n := 3) (f := 2) Nat.prime_three (by norm_num)
    (le_refl 3) (le_refl 2) (by norm_num) (Or.inl rfl) h
  obtain ⟨t, l, n⟩ := labN
  unfold GGTypeARowClass at hc
  simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false, or_false,
    false_or, true_and, and_true] at hc ⊢
  rcases hc with (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | ⟨-, h4⟩ | ⟨h1, h2, h3⟩ | ⟨-, h4⟩ |
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ |
      ⟨h1, h2, h3, h4⟩ | ⟨h, -⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  · exact absurd h4 (by decide)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
  · exact absurd h4 (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))
  · obtain rfl : n = 1 := by omega
    rcases h2 with h2 | h2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, by omega, rfl⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by omega, rfl⟩))))
  · obtain rfl : n = 1 := by omega
    exact absurd h4 (by decide)
  · exact absurd h (by decide)

theorem ggB48_of_sl_two {G : Type} [Group G] [Finite G] {B Bs N : Subgroup G} {m : ℕ}
    (hm : m = 3 ∨ m = 4) (hBs : GGBstar 3 B Bs) (hperf : commutator N = ⊤)
    (hnorm : Bs ≤ Subgroup.normalizer (N : Set G))
    (hmod : StatedClassicalModel (N ⧸ Subgroup.center N) .PSL (m + 1 + 1 + 1) 2 1) :
    48 ≤ Nat.card (ggAutomizer N Bs) := by
  obtain ⟨φ, hφr, hφi⟩ := GGHalf.exists_slLift_two (m := m) (by omega) hperf hmod
  obtain ⟨A, hA⟩ := ggHalf_torusFrame (X := N) (p := 3) rfl hBs (N := m + 1 + 1)
    (by omega) hnorm φ hφr hφi
  have h := GGHalfTorusFrame.card_automizer_ge hA (by omega)
  rcases hm with rfl | rfl <;> (norm_num [Nat.factorial] at h; omega)

section Assembly

theorem ggTableBAut48LeInput_of_omega (hΩ : GGTableBAut48OmegaInput) : GGTableBAut48LeInput := by
  intro G _ _ B Bs x L D J y N hcfg hnbr hinn labJ labN hΛJ hΛN hJ hN hrow hlab
  subst hlab
  have hBs : GGBstar 3 B Bs := hcfg.2.1
  have hq : CFSG.Assembly.IsQuasisimple ↥N := isQuasisimple_of_largeEvenMarking hinn
  rcases ggB48_rows hrow with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (statedClassicalModel_of_hasLabel_typeA hΛN hN)
  · exact Or.inl (statedClassicalModel_of_hasLabel_D32 hN)
  · exact Or.inr (ggB48_of_sp_six_four ggInnerDiagMpInput_holds hBs hinn
      (statedClassicalModel_of_hasLabel_C32 hN))
  · exact hΩ G B Bs x L D J y N hcfg hnbr hinn _ _ hΛJ hΛN hJ hN hrow rfl rfl
  · exact Or.inr (ggB48_of_sl_two (m := 3) (Or.inl rfl) hBs hq.1 hinn.le_normalizer
      (statedClassicalModel_of_hasLabel_typeA hΛN hN))
  · exact Or.inr (ggB48_of_sl_two (m := 4) (Or.inr rfl) hBs hq.1 hinn.le_normalizer
      (statedClassicalModel_of_hasLabel_typeA hΛN hN))

end Assembly

end CFSG.StandardType

end
