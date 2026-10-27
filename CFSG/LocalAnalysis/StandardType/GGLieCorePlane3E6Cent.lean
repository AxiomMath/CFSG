module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
public import CFSG.LocalAnalysis.StandardType.GGFamTame
public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableCRes

theorem ggLieCentIIPlane3_E6 :
    GGLieCentIIPlane3 .E6 := by
  intro L _ _ _ D ρ hρ hfin hq a₁ a₂ h₁ h₂ hp₁ hp₂ hcard J hJ
  obtain ⟨f, hf, hq⟩ := hq
  obtain ⟨S, rfl, rfl⟩ := exists_langSetup_of_datum D ρ hρ hfin hf hq
  have hT : ∀ u : Fin 2, rootDiagUnit Tag.E6
      ((![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ) u) ∈ S.D.torus := by
    intro u
    fin_cases u
    · simpa using h₁
    · simpa using h₂
  have hap : ∀ u : Fin 2, ∀ j, (![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ) u j ^ 3 = 1 := by
    intro u
    fin_cases u
    · exact pow_eq_one_of_rootDiagUnit_pow (a := a₁) (by simpa using hp₁)
    · exact pow_eq_one_of_rootDiagUnit_pow (a := a₂) (by simpa using hp₂)
  have h1 : ∃ u : Fin 2, rootDiagUnit Tag.E6
      ((![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ) u) ≠ 1 := by
    by_contra h
    push Not at h
    have hb₁ : rootDiagUnit Tag.E6 a₁ = 1 := by simpa using h 0
    have hb₂ : rootDiagUnit Tag.E6 a₂ = 1 := by simpa using h 1
    have hbot : Subgroup.closure ({rootDiagUnit Tag.E6 a₁, rootDiagUnit Tag.E6 a₂} :
        Set (ModGL Tag.E6 L)) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_bot.mpr hb₁
      · exact Subgroup.mem_bot.mpr hb₂
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hTame : ∀ i : KernelComponent
        (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ)),
      CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ
          (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ)) i) ∨
        Group.IsSolvable (rationalComponentM S.ρ S.Γ
          (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ)) i) :=
    fun i => langFamTame_of_prime (Or.inl rfl) S Nat.prime_three (by norm_num) hT hap h1 i
  have hJ' : CFSG.Open.IsComponentOf J (S.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : Fin 2 => rootDiagUnit Tag.E6
        ((![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ) u))) := by
    rw [← CFSG.Assembly.isComponentOf_iff_open]
    rw [← centralizer_closure_pair_eq_range (τ := Tag.E6) a₁ a₂]
    exact hJ
  obtain ⟨i', hi', -⟩ := exists_eq_rationalComponentM_of_isComponentOf S Nat.prime_three
    (Or.inl rfl) (by norm_num) hT hap h1 hTame hJ'
  obtain ⟨i, hi⟩ := exists_jointComponent_of_famCharHom a₁ a₂ i'
  refine ⟨i, ?_⟩
  rw [hi']
  rw [ratComp_eq_rationalComponentM]
  have hcomp : rationalComponentM S.ρ S.Γ
        (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ)) i' =
      rationalComponentM S.ρ S.D.Γ (jointChar a₁ a₂) i := by
    unfold rationalComponentM rationalSpanM rationalRootsM
    rw [hi]
    rfl
  exact hcomp

end CFSG.StandardType.LieCore
