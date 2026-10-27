module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableCRes

theorem ggLieFamLabel_E6
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum .E6 L)
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (hρ : FrobRootMap D ρ) (hfin : Finite D.model)
    (hq : ∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) (a₁ a₂ : Fin Tag.E6.rank → Lˣ)
    (h₁ : rootDiagUnit Tag.E6 a₁ ∈ D.torus) (h₂ : rootDiagUnit Tag.E6 a₂ ∈ D.torus)
    (hp₁ : rootDiagUnit Tag.E6 a₁ ^ 3 = 1) (hp₂ : rootDiagUnit Tag.E6 a₂ ^ 3 = 1)
    (hcard : Nat.card ↥(Subgroup.closure
      {rootDiagUnit Tag.E6 a₁, rootDiagUnit Tag.E6 a₂}) = 3 ^ 2)
    (i : KernelComponent (jointChar a₁ a₂))
    (hR : IsQuasisimple ↥(ratComp ρ D.Γ (componentRoots (jointChar a₁ a₂) i))) :
    ∃ n : ℕ, 2 ^ n = D.q ^ componentOrbitLength ρ (componentRoots (jointChar a₁ a₂) i) ∧
      GGCompLabelAt
        (componentLabel (compRank (componentRoots (jointChar a₁ a₂) i))
          (componentRoots (jointChar a₁ a₂) i).ncard
          (twistKindOf ρ (componentRoots (jointChar a₁ a₂) i)) n)
        (ratComp ρ D.Γ (componentRoots (jointChar a₁ a₂) i)) := by
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
  obtain ⟨j, hj⟩ := exists_famComponent_of_jointChar a₁ a₂ i
  have hRj : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ
      (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ)) j) := by
    rw [← ratComp_eq_rationalComponentM]
    rw [← hj]
    exact hR
  have hlab := langFamRatLabel_of_lanes langFamRatLabel_typeA langFamRatLabel_inner
    langFamRatLabel_outerD_high langFamRatLabel_outerD_four langFamRatLabel_outerE
    Tag.E6 L 5 S (Or.inl rfl) 3 Nat.prime_three (by norm_num) (Fin 2)
    (![a₁, a₂] : Fin 2 → Fin Tag.E6.rank → Lˣ) hT hap h1 j hRj
  obtain ⟨n, hn, hGG⟩ := hlab
  refine ⟨n, ?_, ?_⟩
  · rw [hj]; exact hn
  · rw [hj, ratComp_eq_rationalComponentM]
    exact hGG

end CFSG.StandardType.LieCore
