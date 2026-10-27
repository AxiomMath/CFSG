module

public import CFSG.LocalAnalysis.StandardType.GGAllFixedExceptionalToral
public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestExc
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.StandardType.ExcFramesHalf

section Certificates



theorem ggFixedSubgroup_isSolvable_of_recipe_nonTorsion
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp3 : p ≠ 3)
    (hp5 : τ = .E8 → p ≠ 5) (hpq : p ∣ Nat.card K ^ 2 - 1)
    (E : Subgroup (MulAut (TableBExc.RecipeGroup τ K)))
    (hEI : (E : Set (MulAut (TableBExc.RecipeGroup τ K))) ⊆ TableBExc.RecipeID τ K)
    (hE : IsElemAbelian p E)
    (hNPC : CFSG.HasNormalPComplement p
      ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have hinner : E ≤ (MulAut.conj : TableBExc.RecipeGroup τ K →*
      MulAut (TableBExc.RecipeGroup τ K)).range := fun a ha =>
    by
      rcases hτ with rfl | rfl | rfl | rfl
      · exact TableBF4.idImage_subset_inn K (hEI ha)
      · exact mem_range_conj_of_mem_recipeID_E6 hp hp3 (hEI ha) (hE.2 a ha)
      · exact TableBExc.idImage_subset_inn_E7 K (hEI ha)
      · exact TableBExc.idImage_subset_inn_E8 K (hEI ha)
  let eR := TableBExc.recipeEquiv τ K
  let E' : Subgroup (MulAut (adjointGroup τ K)) := E.map (MulAut.congr eR).toMonoidHom
  have hE'range : E' ≤ (MulAut.conj : adjointGroup τ K →*
      MulAut (adjointGroup τ K)).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg⟩ := hinner ha
    refine ⟨eR g, ?_⟩
    rw [← hg]
    exact (mulAut_congr_conj eR g).symm
  let A : Subgroup (adjointGroup τ K) := E'.comap (MulAut.conj :
    adjointGroup τ K →* MulAut (adjointGroup τ K))
  have hconj : Function.Injective (MulAut.conj : adjointGroup τ K →*
      MulAut (adjointGroup τ K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hAmap : A.map (MulAut.conj : adjointGroup τ K →*
      MulAut (adjointGroup τ K)) = E' := Subgroup.map_comap_eq_self hE'range
  have hA : IsElemAbelian p A := (hE.map (MulAut.congr eR).toMonoidHom).comap hconj
  have hfix : ggFixedSubgroup E' =
      Subgroup.centralizer (A : Set (adjointGroup τ K)) := by
    rw [← hAmap, ggFixedSubgroup_map_conj_eq_centralizer]
  have hmapFix : ggFixedSubgroup E' = (ggFixedSubgroup E).map eR.toMonoidHom :=
    ggFixedSubgroup_map_congr eR E
  let eF : ↥(ggFixedSubgroup E) ≃* ↥(ggFixedSubgroup E') :=
    ((ggFixedSubgroup E).equivMapOfInjective eR.toMonoidHom eR.injective).trans
      (MulEquiv.subgroupCongr hmapFix.symm)
  let C : Subgroup (adjointGroup τ K) :=
    Subgroup.centralizer (A : Set (adjointGroup τ K))
  let eC : ↥(ggFixedSubgroup E) ≃* ↥C :=
    eF.trans (MulEquiv.subgroupCongr hfix)
  have hNPC_C : CFSG.HasNormalPComplement p ↥(_root_.commutator ↥C) :=
    CFSG.hasNormalPComplement_of_equiv p eC.commutatorCongr hNPC
  have hsolvC : Group.IsSolvable ↥C :=
    adjoint_full_centralizer_solvable_of_nonTorsion hτ hp hpodd hp3 hp5 hpq A hA hNPC_C
  have hsolvE' : Group.IsSolvable ↥(ggFixedSubgroup E') := by
    rw [hfix]
    exact hsolvC
  have : Group.IsSolvable ↥((ggFixedSubgroup E).map eR.toMonoidHom) := by
    rw [← hmapFix]
    exact hsolvE'
  exact Group.isSolvable_of_isSolvable_injective
    (f := eR.toMonoidHom.subgroupMap (ggFixedSubgroup E))
    (MonoidHom.subgroupMap_injective eR.toMonoidHom _ eR.injective)

theorem largeEvenLabelAll_nonTorsion_fullFixedSolvable
    {tag : LargeEvenLieTag} (htag : tag = .F4 ∨ tag = .E6 ∨ tag = .E7 ∨ tag = .E8)
    {n p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp3 : p ≠ 3)
    (hp5 : tag = .E8 → p ≠ 5) (hpq : p ∣ (2 ^ n) ^ 2 - 1) :
    LargeEvenLabelAll ⟨tag, 0, n⟩ fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E) := by
  rcases htag with rfl | rfl | rfl | rfl
  all_goals
    intro Q hQ
    change LargeEvenRecipeChevalley _ (2 ^ n) false Q at hQ
    refine recipeChevalley_and (P := fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian p E →
        CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E)) ?_ hQ
    intro K _ _ hK E hEI hE hNPC
    have : CharP K 2 := charP_two_of_card hK
    have hpqK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
    first
    | exact ggFixedSubgroup_isSolvable_of_recipe_nonTorsion (τ := .F4)
        (Or.inl rfl) hp hpodd hp3 (by intro h; cases h) hpqK E hEI hE hNPC
    | exact ggFixedSubgroup_isSolvable_of_recipe_nonTorsion (τ := .E6)
        (Or.inr (Or.inl rfl)) hp hpodd hp3 (by intro h; cases h) hpqK E hEI hE hNPC
    | exact ggFixedSubgroup_isSolvable_of_recipe_nonTorsion (τ := .E7)
        (Or.inr (Or.inr (Or.inl rfl))) hp hpodd hp3 (by intro h; cases h) hpqK E hEI hE hNPC
    | exact ggFixedSubgroup_isSolvable_of_recipe_nonTorsion (τ := .E8)
        (Or.inr (Or.inr (Or.inr rfl))) hp hpodd hp3 (fun _ => hp5 rfl)
        hpqK E hEI hE hNPC

theorem isSolvable_inf_centralizer_of_nonTorsion_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hp : p.Prime) (hpodd : Odd p) (hp3 : p ≠ 3)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      (lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧
      lab.rank = 0 ∧ (lab.tag = .E8 → p ≠ 5) ∧ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian p (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab =>
      (lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧
      lab.rank = 0 ∧ (lab.tag = .E8 → p ≠ 5) ∧ p ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E →
      CFSG.HasNormalPComplement p ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab hlab hs => by
      obtain ⟨htag, hrank, hp5, hpq⟩ := hs
      cases lab with
      | mk tag rank n =>
        cases hrank
        exact largeEvenLabelAll_nonTorsion_fullFixedSolvable
          htag hp hpodd hp3 hp5 hpq)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, -, -, hN, hEI, hE⟩, hrow⟩ := hP
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

end Certificates

end CFSG.StandardType
