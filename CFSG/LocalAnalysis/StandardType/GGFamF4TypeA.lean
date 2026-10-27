module

public import CFSG.LocalAnalysis.StandardType.GGFamTypeAField
public import CFSG.LocalAnalysis.StandardType.GGFamTypeAFrames
public import CFSG.LocalAnalysis.StandardType.GGFamF4Orbit
public import CFSG.LocalAnalysis.StandardType.GGFamF4Shapes
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart1

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.F4ExplicitPos.A2Actual CFSG.StandardType.F4ExplicitPos.SelectedLiteral
  CFSG.RankThree.E6 CFSG.RankThree.PartOne.KF4


theorem famF4_laneA1
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hA1 : FamF4PairShape (componentRoots (famCharHom a) i))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAt
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  have hr1 := famF4_pairShape_rankCard hA1
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  exact (fam_fieldSL_rankOne S hρ i hr1.1 hr1.2 hq).toAt

theorem famF4_laneA2
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hA2 : FamF4LongA2Shape (componentRoots (famCharHom a) i) ∨
      FamF4ShortA2Shape (componentRoots (famCharHom a) i))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAt
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  classical
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  rcases hA2 with hLong | hShort
  · obtain ⟨v, hv⟩ := hLong
    set ρA :=
      (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoLong_actual (K := L)) with hρA
    set r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
      fun x y => v • chainRoot f4chainLong x y with hr
    have hψ : IsSLFrame ρA r := by
      rw [hρA, hr]
      exact isSLFrame_long_actual_transport (L := L) v
    have hΨ : componentRoots (famCharHom a) i = frameRoots r := by
      rw [hv, hr, ← frameRoots_f4chainLong_smul (v := v)]
    have hnorm : ∀ x y : Fin 3, x ≠ y → iform (r x y) (r x y) = 2 * (2 : ℤ) := by
      intro x y hxy
      have h1 : iform (r x y) (r x y) =
          iform (chainRoot f4chainLong x y) (chainRoot f4chainLong x y) := by
        rw [hr, iform_smul]
      rw [h1]
      exact (f4_long12_isRoot x y hxy).2.2
    rcases fam_frame_return_cases S hρ i (by norm_num : 3 ≤ 3) hψ (κ := (2 : ℤ))
        (by norm_num) hnorm hΨ with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact (fam_fieldSL_splitFrame S hρ i (by norm_num : 3 ≤ 3) hψ hΨ π hπ hq).toAt
    · exact (fam_fieldSL_unitaryFrame S hρ i (by norm_num : 3 ≤ 3) hψ hΨ π hπ hq).toAt
  · obtain ⟨v, hv⟩ := hShort
    set ρA :=
      (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoShort_actual (K := L)) with hρA
    set r : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ :=
      fun x y => v • f4ShortSigma x y with hr
    have hψ : IsSLFrame ρA r := by
      rw [hρA, hr]
      exact isSLFrame_short_actual_transport (L := L) v
    have hΨ : componentRoots (famCharHom a) i = frameRoots r := by
      rw [hv, hr, ← frameRoots_f4ShortSigma_smul (v := v)]
    have hnorm : ∀ x y : Fin 3, x ≠ y → iform (r x y) (r x y) = 2 * (1 : ℤ) := by
      intro x y hxy
      have h1 : iform (r x y) (r x y) =
          iform (f4ShortSigma x y) (f4ShortSigma x y) := by
        rw [hr, iform_smul]
      rw [h1]
      exact (f4_short_isRoot x y hxy).2.2
    rcases fam_frame_return_cases S hρ i (by norm_num : 3 ≤ 3) hψ (κ := (1 : ℤ))
        (by norm_num) hnorm hΨ with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact (fam_fieldSL_splitFrame S hρ i (by norm_num : 3 ≤ 3) hψ hΨ π hπ hq).toAt
    · exact (fam_fieldSL_unitaryFrame S hρ i (by norm_num : 3 ≤ 3) hψ hΨ π hπ hq).toAt

end CFSG.StandardType.TableCRes
