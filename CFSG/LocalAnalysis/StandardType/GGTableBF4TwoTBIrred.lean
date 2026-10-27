module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBIrredJ
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Two
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLVac
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB TableBSymp

namespace TableBF4TwoTB

theorem isSolvable_centralizer_of_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (x : R) (h : Group.IsSolvable (Subgroup.centralizer ({e x} : Set R'))) :
    Group.IsSolvable (Subgroup.centralizer ({x} : Set R)) := by
  let f : Subgroup.centralizer ({x} : Set R) →* Subgroup.centralizer ({e x} : Set R') :=
    (e.toMonoidHom.comp (Subgroup.centralizer ({x} : Set R)).subtype).codRestrict _ fun c => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
      change (e (c : R)) * e x = e x * e (c : R)
      rw [← map_mul, ← map_mul, hc]
  refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
  exact Subtype.ext (e.injective (congrArg Subtype.val hab))

section Irred


theorem ggTorusIrredSCrJ_F4_two {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hS : GGF4TwoNonToralSolv K) :
    GGTorusIrredSCrJ 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  classical
  refine ggTorusIrredSCrJ_of_secEltSC (TableBF4.idImage_subset_inn K)
    (TableBF4.center_recipeGroup_eq_bot K)
    (ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num)) ?_
  intro E hE hr _ hsc hJE
  have hE' : IsElemAbelian 3 (E.map (TableBF4.recipeEquiv K).toMonoidHom) :=
    TableB.isElemAbelian_map hE _
  have hcard : Nat.card (E.map (TableBF4.recipeEquiv K).toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ (TableBF4.recipeEquiv K).injective).toEquiv).symm
  refine E6TwoTB.SecEltAt.of_map (TableBF4.recipeEquiv K) ?_
  by_cases hconj : ∃ c : adjointGroup .F4 K,
      E.map (TableBF4.recipeEquiv K).toMonoidHom = (tE K).range.map (MulAut.conj c).toMonoidHom
  · obtain ⟨c, hc⟩ := hconj
    rw [hc]
    exact TableBExcTwoTB.secEltAt_map_conj (secEltAt_F4 hK) c
  · exfalso
    obtain ⟨e, heE, he1, hens⟩ := hJE
    refine hens (isSolvable_centralizer_of_mulEquiv (TableBF4.recipeEquiv K) e ?_)
    exact hS _ hE' (hcard ▸ hr) (TableBExcTwoTB.selfCent_map (TableBF4.recipeEquiv K) hsc)
      hconj _ ⟨e, heE, rfl⟩ fun h => he1 ((TableBF4.recipeEquiv K).map_eq_one_iff.mp h)

theorem largeEvenLabelAll_torusIrredSCrJ_f4TwoThree (hS : GGF4TwoNonToralSolvInput) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGTableBF4TwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrredSCrJ p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK])
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 3, TableBF4Two.ggTorusLift_F4Two,
    ggTorusIrredSCrJ_F4_two hK2 (hS K hK2)⟩

theorem excLVac_of_f4TwoThree {p : ℕ} {lab : LargeEvenLabel} (h : GGTableBF4TwoLabel p lab) :
    GGExcLVacLabel p lab :=
  ⟨by rw [h.2.2]; norm_num, Or.inr (Or.inr (Or.inr (Or.inl h.1))), by rw [h.2.1, h.2.2]; norm_num⟩

theorem ggTableBIrredInputOn_f4TwoThree (hS : GGF4TwoNonToralSolvInput) :
    GGTableBIrredInputOn GGTableBF4TwoLabel :=
  ggTableBIrredInputOn_of_labelsSCrJ fun _ _ _ _ h =>
    largeEvenLabelAll_torusIrredSCrJ_f4TwoThree hS h

theorem ggBstarInnerDiagLInputOn_f4TwoThree : GGBstarInnerDiagLInputOn GGTableBF4TwoLabel := by
  have h := ggBstarInnerDiagLInputOn_excLVac GGTableBF4TwoLabel
  have e : (fun p lab => GGTableBF4TwoLabel p lab ∧ GGExcLVacLabel p lab) =
      GGTableBF4TwoLabel :=
    funext fun p => funext fun lab => propext
      ⟨fun h => h.1, fun h => ⟨h, excLVac_of_f4TwoThree h⟩⟩
  rw [e] at h
  exact h

theorem ggTableBCxInputOn_f4TwoThree_holds (hS : GGF4TwoNonToralSolvInput) :
    GGTableBCxInputOn GGTableBF4TwoLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_f4TwoThree
    (ggTableBIrredInputOn_f4TwoThree hS)

theorem ggTableBModuleInputOn_f4TwoThree_holds (hS : GGF4TwoNonToralSolvInput) :
    GGTableBModuleInputOn GGTableBF4TwoLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_f4TwoThree
    (ggTableBIrredInputOn_f4TwoThree hS)

theorem ggTableBActionInputOn_f4TwoThree_holds (hS : GGF4TwoNonToralSolvInput) :
    GGTableBActionInputOn GGTableBF4TwoLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_f4TwoThree
    (ggTableBIrredInputOn_f4TwoThree hS)

theorem largeEvenLabelAll_noLineSCrJ_f4TwoThree (hS : GGF4TwoNonToralSolvInput) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGTableBF4TwoLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineSCrJ p r R I := by
  have hp : p.Prime := h.2.2 ▸ Nat.prime_three
  exact (largeEvenLabelAll_torusIrredSCrJ_f4TwoThree hS h).mono fun _ _ _ _ ⟨r, hl, hi⟩ =>
    ⟨r, hl, ggNoInvariantLineSCrJ_of_irredSCrJ hp hi⟩

theorem ggLNoInvariantLineInputOn_f4TwoThree_holds (hS : GGF4TwoNonToralSolvInput) :
    GGLNoInvariantLineInputOn GGTableBF4TwoLabel :=
  ggLNoInvariantLineInputOn_of_labelsSCrJ fun _ _ _ _ h =>
    largeEvenLabelAll_noLineSCrJ_f4TwoThree hS h

end Irred

end TableBF4TwoTB

end CFSG.StandardType

end
