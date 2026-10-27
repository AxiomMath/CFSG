module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGLabelDef
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelAux
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.MarkingClassical

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irg_hasLabel_classical
    {X : Type} [Group X] {J : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    {t : StatedLieTag} {n g : ℕ} (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨
      t = .POmegaMinus) (hn : RCKNormalizedModel t n g) (φ : (ggU t n g).K →* X)
    (hr : φ.range = J) (hk : φ.ker ≤ Subgroup.center (ggU t n g).K) :
    GGHasLabel (irgLabel t n g) (↥J ⧸ Subgroup.center ↥J) := by
  have hM := irg_lieModel_quot hn.1 hn.2 φ hr hk
  have hcls : CFSG.Open.StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) t n 2 g :=
    hM.statedClassicalModel (by rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide)
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    have h2 : 2 ≤ n := hn.2.2.2.1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ggHasLabel_typeA (n := m) (f := g) hcls
  ·
    have h3 : 3 ≤ n := hn.2.2.2.1
    obtain ⟨-, E, hF, hfin, hcard, ⟨e⟩⟩ := hcls
    obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
    show GGHasLabel ⟨.twA, b, g⟩ _
    exact ⟨E, hF, hfin, hcard, ⟨e⟩⟩
  ·
    obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := hcls
    exact ⟨K, hF, hfin, hcard, ⟨e⟩⟩
  ·
    have h4 : 4 ≤ n := hn.2.2.2
    obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := hcls
    show GGHasLabel ⟨.D, n, g⟩ _
    unfold GGHasLabel LargeEvenRawDatum
    rw [if_neg (by omega : ¬ n = 3)]
    exact ⟨K, hF, hfin, hcard, ⟨e⟩⟩
  ·
    have h4 : 4 ≤ n := hn.2.2.2
    obtain ⟨-, K, hF, hfin, hcard, b, c, hirr, ⟨e⟩⟩ := hcls
    have h2 : ¬ n = 2 := by omega
    have h3 : ¬ n = 3 := by omega
    show GGHasLabel ⟨.twD, n, g⟩ _
    simp only [GGHasLabel, LargeEvenRawDatum]
    rw [if_neg h2, if_neg h3]
    simp only [LargeEvenRecipeOmegaMinus]
    exact ⟨K, hF, hfin, hcard, b, c, hirr, ⟨e.trans (omegaMinusProjEquiv n b c).symm⟩⟩

end CFSG.StandardType.RCKRP
