module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBCard
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3Rows
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3Signed
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA8
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3CD
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3D4
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3U4
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3Linear
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3Unitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem largeEvenLabelAll_A4_notDvdSCJ (n : ℕ) (hn : 3 ∣ 2 ^ n - 1)
    (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.A, 4, n⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 27 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hQ
  refine ⟨K, hKfield, hKfinite, hKcard, hQ, ?_⟩
  have hpK : 3 ∣ Nat.card K - 1 := by
    rw [hKcard]
    exact hn
  have hPSL : GGTorusAutCardSCr 3 3 (projectiveSL 5 K) (Set.range (conjAut 5 K)) 120 := by
    have hfac : Nat.factorial 5 = 120 := by norm_num
    simpa only [hfac] using
      @ggTorusAutCardSCr_PSL 5 3 K _ _ (charP_two_of_card hKcard) (by norm_num) hpK
        (by norm_num)
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 5) K))
      Set.univ, MulAut.congr (TypeA.recipeEquiv 5 K) φ ∈ Set.range (conjAut 5 K) :=
    fun _ hφ => TypeA.congr_recipeEquiv_mem hφ
  have hAut : GGTorusAutCardSCr 3 3 (LargeEvenProj (LargeEvenSLGroup (Fin 5) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 5) K)) Set.univ) 120 :=
    ggTorusAutCardSCr_of_mulEquiv (TypeA.recipeEquiv 5 K) hI hPSL
  exact GGTorusAutCardSCr.notDvdSCJ hAut (by norm_num) (by norm_num)

theorem ggPumpLineAutKnown_A3
    (labJ labX : LargeEvenLabel)
    (hJ : ggResLineJLabel .A3 labJ) (hΛX : LargeEvenInLambda2 labX)
    (hrow : GGTablePRow 3 labJ labX)
    (hoff : ¬ (labX.tag = .twE6 ∧ 3 ∣ 2 ^ labX.n + 1)) :
    LargeEvenLabelAll labX fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 27 := by
  obtain ⟨tJ, rJ, nJ⟩ := labJ
  rcases ggTablePRow_three_A3_not_twE6 hJ hrow hoff with
      ⟨hAJ, h3J, hminus, hrows⟩ | ⟨hDJ, h3J, hminus, hrowD⟩ |
      ⟨htwAJ, h3J, hplus, hrows⟩ | ⟨htwDJ, h3J, hplus, hrowD⟩
  ·
    change tJ = .A at hAJ
    change rJ = 3 at h3J
    subst tJ
    subst rJ
    rcases hrows with hX | hX | hX | hX | hX | ⟨hXA, hXr, h2n, hX3⟩
    · subst labX
      exact largeEvenLabelAll_A4_notDvdSCJ nJ hminus ⟨.A, 3, nJ⟩
    · subst labX
      exact largeEvenLabelAll_A5_notDvdSCJ nJ hΛX.1 hminus
    · subst labX
      exact largeEvenLabelAll_C4_notDvdSCJ nJ (Or.inl hminus) ⟨.A, 3, nJ⟩
    · subst labX
      exact largeEvenLabelAll_D4_notDvdSCJ nJ (Or.inl hminus) ⟨.A, 3, nJ⟩
    · subst labX
      exact largeEvenLabelAll_twD5_notDvdSCJ nJ hΛX.1 hminus ⟨.A, 3, nJ⟩
    ·
      obtain ⟨tX, rX, nX⟩ := labX
      change tX = .A at hXA
      rcases hXr with h7 | h8
      · change rX = 7 at h7
        subst tX
        subst rX
        exact largeEvenLabelAll_A7_notDvdSCJ nX hX3 ⟨.A, 3, nJ⟩
      · change rX = 8 at h8
        subst tX
        subst rX
        exact largeEvenLabelAll_A8_notDvdSCJ (f := nX) hX3 ⟨.A, 3, nJ⟩
  ·
    change tJ = .D at hDJ
    change rJ = 3 at h3J
    subst tJ
    subst rJ
    subst labX
    exact largeEvenLabelAll_D4_notDvdSCJ nJ (Or.inl hminus) ⟨.D, 3, nJ⟩
  ·
    change tJ = .twA at htwAJ
    change rJ = 3 at h3J
    subst tJ
    subst rJ
    rcases hrows with hX | hX | hX | hX | hX
    · subst labX
      exact largeEvenLabelAll_twA4_notDvdSCJ nJ hΛX.1 hplus ⟨.twA, 3, nJ⟩
    · subst labX
      exact largeEvenLabelAll_twA5_notDvdSCJ nJ hΛX.1 hplus
    · subst labX
      exact largeEvenLabelAll_C4_notDvdSCJ nJ (Or.inr hplus) ⟨.twA, 3, nJ⟩
    · subst labX
      exact largeEvenLabelAll_D4_notDvdSCJ nJ (Or.inr hplus) ⟨.twA, 3, nJ⟩
    · subst labX
      exact largeEvenLabelAll_D5_notDvdSCJ nJ hplus ⟨.twA, 3, nJ⟩
  ·
    change tJ = .twD at htwDJ
    change rJ = 3 at h3J
    subst tJ
    subst rJ
    subst labX
    exact largeEvenLabelAll_D4_notDvdSCJ nJ (Or.inr hplus) ⟨.twD, 3, nJ⟩

end CFSG.StandardType
