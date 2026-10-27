module

public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag)

@[expose] noncomputable def FamLabelAt
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) : Prop :=
  ∃ n : ℕ, 2 ^ n = S.D.q ^ componentOrbitLength S.ρ (componentRoots χ i) ∧
    GGCompLabelAt (componentLabel (compRank (componentRoots χ i)) (componentRoots χ i).ncard
      (twistKindOf S.ρ (componentRoots χ i)) n) (rationalComponentM S.ρ S.Γ χ i)

theorem langFamilyCompLabel_conclusion_of_famLabelAt
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ} (i : KernelComponent (famCharHom a))
    {K : Subgroup (ModGL τ L)} (hK : K = rationalComponentM S.ρ S.Γ (famCharHom a) i)
    (h : FamLabelAt S (famCharHom a) i) :
    ∃ n : ℕ, 2 ^ n = S.D.q ^ componentOrbitLength S.ρ
        (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i) ∧
      GGCompLabelAt
        (componentLabel
          (compRank (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i))
          (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i).ncard
          (twistKindOf S.ρ (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i)) n) K := by
  subst hK
  exact h


section Bridge

theorem ggCompLabelAt_A
    {G : Type} [Group G] {X : Subgroup G} (r f : ℕ) (hr : 1 ≤ r) (hf1 : 1 ≤ f) (hf2 : r = 1 → 2 ≤ f)
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) .PSL (r + 1) 2 f) :
    GGCompLabelAt (⟨.A, r, f⟩ : LargeEvenLabel) X := by
  have hc := (LieModel.classical_iff (by simp [classicalTags])).1 h
  refine ⟨⟨hf1, hr, hf2⟩, rfl, ?_, ↥X ⧸ Subgroup.center ↥X, inferInstance, ?_, ⟨MulEquiv.refl _⟩⟩
  · show CFSG.Assembly.LargeEvenRecipeLinear (r + 1) (2 ^ f)
      (fun R _ _ _ => Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* R))
    exact recipeLinear_of_statedClassicalModel hc
  · exact h

theorem ggCompLabelAt_twA
    {G : Type} [Group G] {X : Subgroup G} (r f : ℕ) (hr : 2 ≤ r) (hf1 : 1 ≤ f) (hf2 : r = 2 → 2 ≤ f)
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) .PSU (r + 1) 2 f) :
    GGCompLabelAt (⟨.twA, r, f⟩ : LargeEvenLabel) X := by
  have hc := (LieModel.classical_iff (by simp [classicalTags])).1 h
  refine ⟨⟨hf1, hr, hf2⟩, rfl, ?_, ↥X ⧸ Subgroup.center ↥X, inferInstance, ?_, ⟨MulEquiv.refl _⟩⟩
  · show CFSG.Assembly.LargeEvenRecipeUnitary (r + 1) (2 ^ f)
      (fun R _ _ _ => Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* R))
    exact recipeUnitary_of_statedClassicalModel hc
  · exact h

theorem ggCompLabelAt_D
    {G : Type} [Group G] {X : Subgroup G} (n f : ℕ) (hn : 4 ≤ n) (hf1 : 1 ≤ f)
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) .POmegaPlus n 2 f) :
    GGCompLabelAt (⟨.D, n, f⟩ : LargeEvenLabel) X := by
  have hc := (LieModel.classical_iff (by simp [classicalTags])).1 h
  have h3 : n ≠ 3 := by omega
  refine ⟨⟨hf1, (by omega : 3 ≤ n)⟩, rfl, ?_, ↥X ⧸ Subgroup.center ↥X, inferInstance, ?_,
    ⟨MulEquiv.refl _⟩⟩
  · show if n = 3 then _ else _
    simp only [h3, ↓reduceIte]
    exact recipeOmegaPlus_of_statedClassicalModel hc
  · have e1 : markTag (⟨.D, n, f⟩ : LargeEvenLabel) = .POmegaPlus := by simp [markTag, h3]
    have e2 : markRank (⟨.D, n, f⟩ : LargeEvenLabel) = n := by simp [markRank, h3]
    show LieModel _ (markTag ⟨.D, n, f⟩) (markRank ⟨.D, n, f⟩) 2 f
    rw [e1, e2]
    exact h

theorem ggCompLabelAt_twD
    {G : Type} [Group G] {X : Subgroup G} (n f : ℕ) (hn : 4 ≤ n) (hf1 : 1 ≤ f)
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus n 2 f) :
    GGCompLabelAt (⟨.twD, n, f⟩ : LargeEvenLabel) X := by
  have hc := (LieModel.classical_iff (by simp [classicalTags])).1 h
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  refine ⟨⟨hf1, (by omega : 2 ≤ n)⟩, rfl, ?_, ↥X ⧸ Subgroup.center ↥X, inferInstance, ?_,
    ⟨MulEquiv.refl _⟩⟩
  · show if n = 2 then _ else if n = 3 then _ else _
    simp only [h2, h3, ↓reduceIte]
    exact recipeOmegaMinus_of_statedClassicalModel hc
  · have e1 : markTag (⟨.twD, n, f⟩ : LargeEvenLabel) = .POmegaMinus := by simp [markTag, h2, h3]
    have e2 : markRank (⟨.twD, n, f⟩ : LargeEvenLabel) = n := by simp [markRank, h2, h3]
    have e3 : markDeg (⟨.twD, n, f⟩ : LargeEvenLabel) = f := by simp [markDeg, h2]
    show LieModel _ (markTag ⟨.twD, n, f⟩) (markRank ⟨.twD, n, f⟩) 2 (markDeg ⟨.twD, n, f⟩)
    rw [e1, e2, e3]
    exact h

theorem ggCompLabelAt_E6
    {G : Type} [Group G] {X : Subgroup G} (f : ℕ) (hf1 : 1 ≤ f)
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) .E6 0 2 f) :
    GGCompLabelAt (⟨.E6, 0, f⟩ : LargeEvenLabel) X := by
  have hc := ((LieModel.chevalleyExceptional_iff (t := .E6) (by decide)).1 h).2
  refine ⟨⟨hf1, rfl⟩, rfl, ?_, ↥X ⧸ Subgroup.center ↥X, inferInstance, h, ⟨MulEquiv.refl _⟩⟩
  exact recipeChevalley_of_untwistedChevalleyModel .E6 hc.2

theorem ggCompLabelAt_E7
    {G : Type} [Group G] {X : Subgroup G} (f : ℕ) (hf1 : 1 ≤ f)
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) .E7 0 2 f) :
    GGCompLabelAt (⟨.E7, 0, f⟩ : LargeEvenLabel) X := by
  have hc := ((LieModel.chevalleyExceptional_iff (t := .E7) (by decide)).1 h).2
  refine ⟨⟨hf1, rfl⟩, rfl, ?_, ↥X ⧸ Subgroup.center ↥X, inferInstance, h, ⟨MulEquiv.refl _⟩⟩
  exact recipeChevalley_of_untwistedChevalleyModel .E7 hc.2

theorem ggCompLabelAt_E8
    {G : Type} [Group G] {X : Subgroup G} (f : ℕ) (hf1 : 1 ≤ f)
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) .E8 0 2 f) :
    GGCompLabelAt (⟨.E8, 0, f⟩ : LargeEvenLabel) X := by
  have hc := ((LieModel.chevalleyExceptional_iff (t := .E8) (by decide)).1 h).2
  refine ⟨⟨hf1, rfl⟩, rfl, ?_, ↥X ⧸ Subgroup.center ↥X, inferInstance, h, ⟨MulEquiv.refl _⟩⟩
  exact recipeChevalley_of_untwistedChevalleyModel .E8 hc.2

theorem ggCompLabelAt_twE6
    {G : Type} [Group G] {X : Subgroup G} (f : ℕ) (hf1 : 1 ≤ f)
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) .twistedE6 0 2 f) :
    GGCompLabelAt (⟨.twE6, 0, f⟩ : LargeEvenLabel) X := by
  have hc := ((LieModel.chevalleyExceptional_iff (t := .twistedE6) (by decide)).1 h).2
  refine ⟨⟨hf1, rfl⟩, rfl, ?_, ↥X ⧸ Subgroup.center ↥X, inferInstance, h, ⟨MulEquiv.refl _⟩⟩
  exact recipeTwisted_of_twistedChevalleyModel .E6 hc.2

theorem ggCompLabelAt_triD4
    {G : Type} [Group G] {X : Subgroup G} (f : ℕ) (hf1 : 1 ≤ f)
    (h : LieModel (↥X ⧸ Subgroup.center ↥X) .trialityD4 0 2 f) :
    GGCompLabelAt (⟨.triD4, 0, f⟩ : LargeEvenLabel) X := by
  have hc := ((LieModel.chevalleyExceptional_iff (t := .trialityD4) (by decide)).1 h).2
  refine ⟨⟨hf1, rfl⟩, rfl, ?_, ↥X ⧸ Subgroup.center ↥X, inferInstance, h, ⟨MulEquiv.refl _⟩⟩
  exact recipeTwisted_of_twistedChevalleyModel .D4 hc.2

end Bridge

end CFSG.StandardType.TableCRes

end
