module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTvFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB TableBSymp Matrix TableBExcTwo
  TableBExcTwoTv

namespace TableBExcTwoTB

section Labels

@[expose] def GGE7TwoNormIsometry (K : Type) [Field K] [CharP K 2] : Prop :=
  ∀ φ : MulAut (adjointGroup .E7 K),
    (∀ x ∈ (tE K frameE7).range, φ x ∈ (tE K frameE7).range) →
      ∃ M : (Fin (6 + 1) → ZMod 3) →+ (Fin (6 + 1) → ZMod 3),
        (∀ v, φ (tE K frameE7 (Multiplicative.ofAdd v)) =
          tE K frameE7 (Multiplicative.ofAdd (M v))) ∧
        ∀ v w, M v ⬝ᵥ M w = v ⬝ᵥ w

@[expose] def GGE8TwoNormIsometry (K : Type) [Field K] [CharP K 2] : Prop :=
  ∀ φ : MulAut (adjointGroup .E8 K),
    (∀ x ∈ (tE K frameE8).range, φ x ∈ (tE K frameE8).range) →
      ∃ M : (Fin (7 + 1) → ZMod 3) →+ (Fin (7 + 1) → ZMod 3),
        (∀ v, φ (tE K frameE8 (Multiplicative.ofAdd v)) =
          tE K frameE8 (Multiplicative.ofAdd (M v))) ∧
        ∀ v w, M v ⬝ᵥ M w = v ⬝ᵥ w

@[expose] def GGE7TwoNormIsometryInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → GGE7TwoNormIsometry K

@[expose] def GGE8TwoNormIsometryInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → GGE8TwoNormIsometry K

theorem ggNoTransvectionSCr_E7_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hE7 : GGE7TwoSCToral K) (hN : GGE7TwoNormIsometry K) :
    GGNoTransvectionSCr 3 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  have hcp : GGCenterPrime 3 (adjointGroup .E7 K) :=
    ggCenterPrime_of_mulEquiv_tv (TableBExc.recipeEquiv .E7 K).symm
      (ExcSplitL.ggCenterPrime_recipe_E7 (K := K) (f := 1) le_rfl (by rw [hK]; norm_num)
        Nat.prime_three (by norm_num))
  have hadj : GGNoTransvectionSCr 3 6 (adjointGroup .E7 K)
      (Set.range (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))) :=
    ggNoTransvectionSCr_of_frameTorus subset_rfl
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E7) (K := K))
      hcp (tE_injective frameE7) (fun E hE hr hsc => hE7 E hE hr hsc) hN
  refine ggNoTransvectionSCr_of_mulEquiv (TableBExc.recipeEquiv .E7 K) ?_ hadj
  intro φ hφ
  obtain ⟨g, rfl⟩ := recipeID_subset_inn_two .E7 hK hφ
  refine ⟨(TableBExc.recipeEquiv .E7 K) g, ?_⟩
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]

theorem ggNoTransvectionSCr_E8_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (hE8 : GGE8TwoSCToral K) (hN : GGE8TwoNormIsometry K) :
    GGNoTransvectionSCr 3 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have hcp : GGCenterPrime 3 (adjointGroup .E8 K) :=
    ggCenterPrime_of_mulEquiv_tv (TableBExc.recipeEquiv .E8 K).symm
      (ExcSplitL.ggCenterPrime_recipe_E8 (K := K) Nat.prime_three (by norm_num))
  have hadj : GGNoTransvectionSCr 3 7 (adjointGroup .E8 K)
      (Set.range (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))) :=
    ggNoTransvectionSCr_of_frameTorus subset_rfl
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := K))
      hcp (tE_injective frameE8) (fun E hE hr hsc => hE8 E hE hr hsc) hN
  refine ggNoTransvectionSCr_of_mulEquiv (TableBExc.recipeEquiv .E8 K) ?_ hadj
  intro φ hφ
  obtain ⟨g, rfl⟩ := recipeID_subset_inn_two .E8 hK hφ
  refine ⟨(TableBExc.recipeEquiv .E8 K) g, ?_⟩
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]

theorem largeEvenLabelAll_noTransvectionSCr_e7TwoThree (hE7 : GGE7TwoSCToralInput)
    (hN7 : GGE7TwoNormIsometryInput) {p : ℕ} {lab : LargeEvenLabel} (h : GGE7TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoTransvectionSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 6, TableBExcTwo.ggTorusLift_E7Two,
    ggNoTransvectionSCr_E7_two hK (hE7 K hK) (hN7 K hK)⟩

theorem largeEvenLabelAll_noTransvectionSCr_e8TwoThree (hE8 : GGE8TwoSCToralInput)
    (hN8 : GGE8TwoNormIsometryInput) {p : ℕ} {lab : LargeEvenLabel} (h : GGE8TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoTransvectionSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 7, TableBExcTwo.ggTorusLift_E8Two,
    ggNoTransvectionSCr_E8_two hK (hE8 K hK) (hN8 K hK)⟩

theorem ggLTransvectionCenterInputOn_e7TwoThree_holds (hE7 : GGE7TwoSCToralInput)
    (hN7 : GGE7TwoNormIsometryInput) : GGLTransvectionCenterInputOn GGE7TwoThreeLabel :=
  TwE6TB.ggLTransvectionCenterInputOn_of_labelsSCr' ggLNoncyclicInput_holds fun _ _ _ _ h =>
    largeEvenLabelAll_noTransvectionSCr_e7TwoThree hE7 hN7 h

theorem ggLTransvectionCenterInputOn_e8TwoThree_holds (hE8 : GGE8TwoSCToralInput)
    (hN8 : GGE8TwoNormIsometryInput) : GGLTransvectionCenterInputOn GGE8TwoThreeLabel :=
  TwE6TB.ggLTransvectionCenterInputOn_of_labelsSCr' ggLNoncyclicInput_holds fun _ _ _ _ h =>
    largeEvenLabelAll_noTransvectionSCr_e8TwoThree hE8 hN8 h

theorem ggLTransvectionCenterInputOn_of_not_e7TwoThree_tv (hE7 : GGE7TwoSCToralInput)
    (hN7 : GGE7TwoNormIsometryInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab => S p lab ∧ ¬ GGE7TwoThreeLabel p lab) :
    GGLTransvectionCenterInputOn S := by
  have h' := (ggLTransvectionCenterInputOn_e7TwoThree_holds hE7 hN7).or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGE7TwoThreeLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

theorem ggLTransvectionCenterInputOn_of_not_e8TwoThree_tv (hE8 : GGE8TwoSCToralInput)
    (hN8 : GGE8TwoNormIsometryInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab => S p lab ∧ ¬ GGE8TwoThreeLabel p lab) :
    GGLTransvectionCenterInputOn S := by
  have h' := (ggLTransvectionCenterInputOn_e8TwoThree_holds hE8 hN8).or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGE8TwoThreeLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

theorem ggLTransvectionCenterInputOn_of_not_e7e8TwoThree_tv (hE7 : GGE7TwoSCToralInput)
    (hN7 : GGE7TwoNormIsometryInput) (hE8 : GGE8TwoSCToralInput)
    (hN8 : GGE8TwoNormIsometryInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab =>
      (S p lab ∧ ¬ GGE7TwoThreeLabel p lab) ∧ ¬ GGE8TwoThreeLabel p lab) :
    GGLTransvectionCenterInputOn S :=
  ggLTransvectionCenterInputOn_of_not_e7TwoThree_tv hE7 hN7
    (ggLTransvectionCenterInputOn_of_not_e8TwoThree_tv hE8 hN8 h)

end Labels

end TableBExcTwoTB

end CFSG.StandardType

end
