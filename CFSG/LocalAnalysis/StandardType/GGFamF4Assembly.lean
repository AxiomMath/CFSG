module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs
public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamF4Orbit
public import CFSG.LocalAnalysis.StandardType.GGFamF4Shapes
public import CFSG.LocalAnalysis.StandardType.GGFamF4TypeA
public import CFSG.LocalAnalysis.StandardType.GGFamF4B2
public import CFSG.LocalAnalysis.StandardType.GGFamF4RankThree
public import CFSG.LocalAnalysis.StandardType.GGFamF4Tame
public import CFSG.LocalAnalysis.StandardType.GGFamF4Trivial

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem langFamRatCompFieldF4_holds
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAt
        (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
        (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
      (S.D.q = 2 ∧ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 ∧
        Nat.card ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) = 360 ∧
        Nat.card (↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) = 360) := by
  rcases famF4_shape S hp hp2 hT hap h1 i with hA1 | hLong | hShort | hB2 | hB3 | hC3
  · exact Or.inl (famF4_laneA1 S hp hp2 hT hap h1 i hA1 hq)
  · exact Or.inl (famF4_laneA2 S hp hp2 hT hap h1 i (Or.inl hLong) hq)
  · exact Or.inl (famF4_laneA2 S hp hp2 hT hap h1 i (Or.inr hShort) hq)
  · exact famF4_laneB2 S hp hp2 hT hap h1 i hB2 hq
  · exact Or.inl (famF4_laneRankThree S hp hp2 hT hap h1 i (Or.inl hB3) hq)
  · exact Or.inl (famF4_laneRankThree S hp hp2 hT hap h1 i (Or.inr hC3) hq)

theorem langFamilyCompFieldF4_holds :
    LangFamilyCompFieldF4 := by
  intro L _ _ _ p₀ p S hp hp2 ι a hT hap K hK
  by_cases h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1
  · have hTame : ∀ i : KernelComponent (famCharHom a),
        CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
          Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
      fun i => langFamTame_F4 S hp hp2 hT hap h1 i
    obtain ⟨i, hKi, hq⟩ :=
      exists_eq_rationalComponentM_of_isComponentOf_gen S hp (Or.inl rfl) hp2 hT hap h1 hTame hK
    refine ⟨i, ?_, ?_⟩
    · rw [hKi]
      exact (Subgroup.commutator_le_self _).trans inf_le_left
    · rw [hKi]
      exact langFamRatCompFieldF4_holds S hp hp2 hT hap h1 i hq
  · push Not at h1
    exact langFamilyCompFieldF4_trivial S a h1 K hK

end CFSG.StandardType.TableCRes
