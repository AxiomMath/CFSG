module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Shapes
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Orbit
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4TameSuN
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamTameInner
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableCRes
open CFSG.Open (StatedLieTag)

private theorem l10lF4_exc_rank {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i : KernelComponent χ} (hk : twistKindM ρ χ i = .exc) :
    compRank (componentRoots χ i) = 6 ∨ compRank (componentRoots χ i) = 4 := by
  unfold twistKindM at hk
  split_ifs at hk with h1 h2
  rcases h2 with ⟨hr, -⟩ | ⟨hr, -⟩
  · exact Or.inl hr
  · exact Or.inr hr

theorem ggLieF4Plane_tame
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    (i : KernelComponent (jointChar a₁ a₂)) :
    IsQuasisimple ↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ∨
      Group.IsSolvable ↥(GGLieF4PlaneRat D ρ a₁ a₂ i) := by
  obtain ⟨f, hf, hq⟩ := h.hq
  obtain ⟨S, rfl, rfl⟩ := exists_langSetup_of_datum D ρ h.frob h.finite hf hq
  have hT : ∀ u : Fin 2, rootDiagUnit Tag.F4
      ((![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ) u) ∈ S.D.torus := by
    intro u
    fin_cases u
    · simpa using h.mem₁
    · simpa using h.mem₂
  have hap : ∀ u : Fin 2, ∀ j, (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ) u j ^ 3 = 1 := by
    intro u
    fin_cases u
    · exact pow_eq_one_of_rootDiagUnit_pow (a := a₁) (by simpa using h.pow₁)
    · exact pow_eq_one_of_rootDiagUnit_pow (a := a₂) (by simpa using h.pow₂)
  have h1 : ∃ u : Fin 2, rootDiagUnit Tag.F4
      ((![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ) u) ≠ 1 := by
    by_contra hc
    push Not at hc
    have hb₁ : rootDiagUnit Tag.F4 a₁ = 1 := by simpa using hc 0
    have hb₂ : rootDiagUnit Tag.F4 a₂ = 1 := by simpa using hc 1
    have hbot : Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
        Set (ModGL Tag.F4 L)) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_bot.mpr hb₁
      · exact Subgroup.mem_bot.mpr hb₂
    have hcard := h.card
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨i', hi'⟩ := exists_famComponent_of_jointChar a₁ a₂ i
  have hshape : GGLieF4PlaneShape
      (componentRoots (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i') := by
    have h0 := ggLieF4Plane_shape h i
    rwa [hi'] at h0
  have hrat : GGLieF4PlaneRat S.D S.ρ a₁ a₂ i =
      rationalComponentM S.ρ S.Γ
        (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i' := by
    unfold GGLieF4PlaneRat
    rw [ratComp_eq_rationalComponentM]
    unfold rationalComponentM rationalSpanM rationalRootsM
    rw [hi']
    rfl
  rw [hrat]
  cases hk : twistKindM S.ρ
      (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i' with
  | inner =>
    refine langFamTame_inner_of_hp5 S Nat.prime_three ?_ hT hap h1 i' hk
    intro hG
    exact absurd hG (by decide)
  | suN =>
    exact langFamTame_suN_F4 S (hT 0) (hT 1) (hap 0) (hap 1) h.card i' hk
  | twoD =>
    obtain ⟨-, h4, -⟩ := twistKindM_twoD_unpack S.ρ hk
    unfold GGLieF4PlaneShape at hshape
    rcases hshape with ⟨hr, -⟩ | ⟨hr, -⟩ | ⟨hr, -⟩ <;> omega
  | exc =>
    rcases l10lF4_exc_rank S.ρ hk with hr | hr
    · unfold GGLieF4PlaneShape at hshape
      rcases hshape with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    · unfold GGLieF4PlaneShape at hshape
      rcases hshape with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega

theorem ggLieCentIIPlane3_F4 :
    GGLieCentIIPlane3 .F4 := by
  intro L _ _ _ D ρ hρ hfin hq a₁ a₂ h₁ h₂ hp₁ hp₂ hcard J hJ
  have hH : GGLieF4PlaneHyp D ρ a₁ a₂ := ⟨hρ, hfin, hq, h₁, h₂, hp₁, hp₂, hcard⟩
  obtain ⟨f, hf, hq⟩ := hq
  obtain ⟨S, rfl, rfl⟩ := exists_langSetup_of_datum D ρ hρ hfin hf hq
  have hT : ∀ u : Fin 2, rootDiagUnit Tag.F4
      ((![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ) u) ∈ S.D.torus := by
    intro u
    fin_cases u
    · simpa using h₁
    · simpa using h₂
  have hap : ∀ u : Fin 2, ∀ j, (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ) u j ^ 3 = 1 := by
    intro u
    fin_cases u
    · exact pow_eq_one_of_rootDiagUnit_pow (a := a₁) (by simpa using hp₁)
    · exact pow_eq_one_of_rootDiagUnit_pow (a := a₂) (by simpa using hp₂)
  have h1 : ∃ u : Fin 2, rootDiagUnit Tag.F4
      ((![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ) u) ≠ 1 := by
    by_contra h
    push Not at h
    have hb₁ : rootDiagUnit Tag.F4 a₁ = 1 := by simpa using h 0
    have hb₂ : rootDiagUnit Tag.F4 a₂ = 1 := by simpa using h 1
    have hbot : Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
        Set (ModGL Tag.F4 L)) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_bot.mpr hb₁
      · exact Subgroup.mem_bot.mpr hb₂
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hkey : ∀ i' : KernelComponent (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)),
      ∃ i : KernelComponent (jointChar a₁ a₂),
        rationalComponentM S.ρ S.Γ
            (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i' =
          ratComp S.ρ S.D.Γ (componentRoots (jointChar a₁ a₂) i) := by
    intro i'
    obtain ⟨i, hi⟩ := exists_jointComponent_of_famCharHom a₁ a₂ i'
    refine ⟨i, ?_⟩
    rw [ratComp_eq_rationalComponentM]
    unfold rationalComponentM rationalSpanM rationalRootsM
    rw [hi]
    rfl
  have hTame : ∀ i' : KernelComponent
        (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)),
      CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ
          (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i') ∨
        Group.IsSolvable (rationalComponentM S.ρ S.Γ
          (famCharHom (![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ)) i') := by
    intro i'
    obtain ⟨i, hi⟩ := hkey i'
    rw [hi]
    exact ggLieF4Plane_tame hH i
  have hJ' : CFSG.Open.IsComponentOf J (S.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : Fin 2 => rootDiagUnit Tag.F4
        ((![a₁, a₂] : Fin 2 → Fin Tag.F4.rank → Lˣ) u))) := by
    rw [← CFSG.Assembly.isComponentOf_iff_open]
    rw [← centralizer_closure_pair_eq_range (τ := Tag.F4) a₁ a₂]
    exact hJ
  obtain ⟨i', hi', -⟩ := exists_eq_rationalComponentM_of_isComponentOf_gen S Nat.prime_three
    (Or.inl rfl) (by norm_num) hT hap h1 hTame hJ'
  obtain ⟨i, hi⟩ := hkey i'
  exact ⟨i, hi'.trans hi⟩

end CFSG.StandardType.LieCore
