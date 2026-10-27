module

public import CFSG.LieType.AlgebraicGroups.E6TwoSevenCentralizer
public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem ggFixedSubgroup_isSolvable_of_recipe_E6Seven
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (E : Subgroup (MulAut (TableBExc.RecipeGroup .E6 K)))
    (hEI : (E : Set (MulAut (TableBExc.RecipeGroup .E6 K))) ⊆ TableBExc.RecipeID .E6 K)
    (hE : IsElemAbelian 7 E) (hcard : 7 ^ 3 ≤ Nat.card E) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp (by
    rw [Nat.card_units, hK])).1
  have hT : TableB.torusSubgroup Tag.E6.cartan K = ⊤ := by
    rw [eq_top_iff]
    intro a ha
    have ha1 : a = 1 := Subsingleton.elim _ _
    rw [ha1]
    exact one_mem _
  have hinner : E ≤ (MulAut.conj : TableBExc.RecipeGroup .E6 K →*
      MulAut (TableBExc.RecipeGroup .E6 K)).range := fun a ha =>
    TableBExc.idImage_subset_inn_of_top .E6 K hT (hEI ha)
  let eR := TableBExc.recipeEquiv .E6 K
  let E' : Subgroup (MulAut (adjointGroup .E6 K)) := E.map (MulAut.congr eR).toMonoidHom
  have hE'range : E' ≤ (MulAut.conj : adjointGroup .E6 K →*
      MulAut (adjointGroup .E6 K)).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg⟩ := hinner ha
    refine ⟨eR g, ?_⟩
    rw [← hg]
    exact (mulAut_congr_conj eR g).symm
  let A : Subgroup (adjointGroup .E6 K) := E'.comap (MulAut.conj :
    adjointGroup .E6 K →* MulAut (adjointGroup .E6 K))
  have hconj : Function.Injective (MulAut.conj : adjointGroup .E6 K →*
      MulAut (adjointGroup .E6 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hAmap : A.map (MulAut.conj : adjointGroup .E6 K →*
      MulAut (adjointGroup .E6 K)) = E' := Subgroup.map_comap_eq_self hE'range
  have hA : IsElemAbelian 7 A := (hE.map (MulAut.congr eR).toMonoidHom).comap hconj
  have hAcard : 7 ^ 3 ≤ Nat.card A := by
    have h1 : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective (MulAut.congr eR).injective
    have h2 : Nat.card A = Nat.card E' := by
      rw [← hAmap]
      exact (Subgroup.card_map_of_injective hconj).symm
    rwa [h2, h1]
  have hfix : ggFixedSubgroup E' = Subgroup.centralizer (A : Set (adjointGroup .E6 K)) := by
    rw [← hAmap, ggFixedSubgroup_map_conj_eq_centralizer]
  have hsolv : Group.IsSolvable ↥(ggFixedSubgroup E') := by
    rw [hfix]
    exact CFSG.LieType.AlgebraicGroups.E6TwoSeven.e6_two_seven_full_centralizer_solvable
      K hK A hA hAcard
  haveI : Group.IsSolvable ↥((ggFixedSubgroup E).map eR.toMonoidHom) := by
    have hmapFix : ggFixedSubgroup E' = (ggFixedSubgroup E).map eR.toMonoidHom :=
      ggFixedSubgroup_map_congr eR E
    rw [← hmapFix]
    exact hsolv
  exact Group.isSolvable_of_isSolvable_injective
    (f := eR.toMonoidHom.subgroupMap (ggFixedSubgroup E))
    (MonoidHom.subgroupMap_injective eR.toMonoidHom _ eR.injective)

theorem largeEvenLabelAll_E6Seven_fullFixedSolvable :
    LargeEvenLabelAll ⟨.E6, 0, 1⟩ fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian 7 E →
        7 ^ 3 ≤ Nat.card E → Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  change LargeEvenRecipeChevalley Tag.E6.cartan 2 false Q at hQ
  refine recipeChevalley_and (P := fun R _ I _ =>
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian 7 E →
      7 ^ 3 ≤ Nat.card E → Group.IsSolvable ↥(ggFixedSubgroup E)) ?_ hQ
  intro K _ _ hK E hEI hE hcard
  exact ggFixedSubgroup_isSolvable_of_recipe_E6Seven hK E hEI hE hcard

theorem isSolvable_inf_centralizer_of_E6Seven_marking
    {G : Type} [Group G] {Bs X : Subgroup G}
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      lab = ⟨.E6, 0, 1⟩ ∧ ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian 7 (ggBeta (G := G) (L := X) θ hN).range ∧
        7 ^ 3 ≤ Nat.card (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => lab = ⟨.E6, 0, 1⟩)
    (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian 7 E → 7 ^ 3 ≤ Nat.card E →
        Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab _ hlab => by subst lab; exact largeEvenLabelAll_E6Seven_fullFixedSolvable)
    (fun _ _ _ _ _ _ h => h.1) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ := largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, hN, hEI, hE, hcard⟩, hrow⟩ := hP
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ
    (hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE hcard)

end CFSG.StandardType
