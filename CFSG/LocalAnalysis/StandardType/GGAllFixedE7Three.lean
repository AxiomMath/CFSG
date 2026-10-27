module

public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGAllFixedExceptionalToral
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
public import CFSG.LieType.Chevalley.E7Three.CentralizerFiniteTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.StandardType.ExcFramesHalf

section Certificates


theorem e7_three_adjoint_full_centralizer_solvable
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (A : Subgroup (adjointGroup .E7 K)) (hA : IsElemAbelian 3 A)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 K))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup .E7 K))) := by
  classical
  by_cases hT : IsToralSubgroup .E7 (AlgebraicClosure K)
      (A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E7 K).subtype))
  · have h3 : 3 ∣ Nat.card K ^ 2 - 1 := by
      change 3 ∣ Nat.card K ^ 2 - 1 ^ 2
      rw [Nat.sq_sub_sq]
      rcases OrthTorus.three_dvd_card_sub_or_add (K := K) with h | h
      · exact dvd_mul_of_dvd_right h _
      · exact dvd_mul_of_dvd_left h _
    exact adjoint_full_toral_centralizer_solvable
      (Or.inr (Or.inr (Or.inl rfl))) Nat.prime_three (by decide) h3 A hA.2 hT hNPC
  · exact E7Three.Centralizer.isSolvable_centralizer_of_not_toral A
      (fun x hx y hy => hA.comm hx hy) hA.2 hT hNPC

theorem ggFixedSubgroup_isSolvable_of_recipe_E7Three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (E : Subgroup (MulAut (TableBExc.RecipeGroup .E7 K)))
    (hEI : (E : Set (MulAut (TableBExc.RecipeGroup .E7 K))) ⊆ TableBExc.RecipeID .E7 K)
    (hE : IsElemAbelian 3 E)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have hinner : E ≤ (MulAut.conj : TableBExc.RecipeGroup .E7 K →*
      MulAut (TableBExc.RecipeGroup .E7 K)).range := fun a ha =>
    TableBExc.idImage_subset_inn_E7 K (hEI ha)
  let eR := TableBExc.recipeEquiv .E7 K
  let E' : Subgroup (MulAut (adjointGroup .E7 K)) := E.map (MulAut.congr eR).toMonoidHom
  have hE'range : E' ≤ (MulAut.conj : adjointGroup .E7 K →*
      MulAut (adjointGroup .E7 K)).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg⟩ := hinner ha
    refine ⟨eR g, ?_⟩
    rw [← hg]
    exact (mulAut_congr_conj eR g).symm
  let A : Subgroup (adjointGroup .E7 K) := E'.comap (MulAut.conj :
    adjointGroup .E7 K →* MulAut (adjointGroup .E7 K))
  have hconj : Function.Injective (MulAut.conj : adjointGroup .E7 K →*
      MulAut (adjointGroup .E7 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hAmap : A.map (MulAut.conj : adjointGroup .E7 K →*
      MulAut (adjointGroup .E7 K)) = E' := Subgroup.map_comap_eq_self hE'range
  have hA : IsElemAbelian 3 A := (hE.map (MulAut.congr eR).toMonoidHom).comap hconj
  have hfix : ggFixedSubgroup E' =
      Subgroup.centralizer (A : Set (adjointGroup .E7 K)) := by
    rw [← hAmap, ggFixedSubgroup_map_conj_eq_centralizer]
  have hmapFix : ggFixedSubgroup E' = (ggFixedSubgroup E).map eR.toMonoidHom :=
    ggFixedSubgroup_map_congr eR E
  let eF : ↥(ggFixedSubgroup E) ≃* ↥(ggFixedSubgroup E') :=
    ((ggFixedSubgroup E).equivMapOfInjective eR.toMonoidHom eR.injective).trans
      (MulEquiv.subgroupCongr hmapFix.symm)
  let C : Subgroup (adjointGroup .E7 K) :=
    Subgroup.centralizer (A : Set (adjointGroup .E7 K))
  let eC : ↥(ggFixedSubgroup E) ≃* ↥C :=
    eF.trans (MulEquiv.subgroupCongr hfix)
  have hNPC_C : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥C) :=
    CFSG.hasNormalPComplement_of_equiv 3 eC.commutatorCongr hNPC
  have hsolvC : Group.IsSolvable ↥C :=
    e7_three_adjoint_full_centralizer_solvable A hA hNPC_C
  have hsolvE' : Group.IsSolvable ↥(ggFixedSubgroup E') := by
    rw [hfix]
    exact hsolvC
  have : Group.IsSolvable ↥((ggFixedSubgroup E).map eR.toMonoidHom) := by
    rw [← hmapFix]
    exact hsolvE'
  exact Group.isSolvable_of_isSolvable_injective
    (f := eR.toMonoidHom.subgroupMap (ggFixedSubgroup E))
    (MonoidHom.subgroupMap_injective eR.toMonoidHom _ eR.injective)

theorem largeEvenLabelAll_E7Three_fullFixedSolvable {n : ℕ} :
    LargeEvenLabelAll ⟨.E7, 0, n⟩ fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian 3 E →
        CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  change LargeEvenRecipeChevalley (LargeEvenCartanE 7) (2 ^ n) false Q at hQ
  refine recipeChevalley_and (P := fun R _ I _ =>
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I → IsElemAbelian 3 E →
      CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E)) ?_ hQ
  intro K _ _ hK E hEI hE hNPC
  have : CharP K 2 := charP_two_of_card hK
  exact ggFixedSubgroup_isSolvable_of_recipe_E7Three (K := K) E hEI hE hNPC

theorem isSolvable_inf_centralizer_of_E7Three_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      lab.tag = .E7 ∧ lab.rank = 0 ∧ p = 3 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian 3 (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .E7 ∧ lab.rank = 0 ∧ p = 3)
    (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian 3 E →
      CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab _ hs => by
      obtain ⟨htag, hrank, -⟩ := hs
      cases lab with
      | mk tag rank n =>
        cases htag
        cases hrank
        exact largeEvenLabelAll_E7Three_fullFixedSolvable (n := n))
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) hmark
  obtain ⟨lab, _, _, R, _, I, _, θ, hP⟩ := largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hp3, hN, hEI, hE⟩, hrow⟩ := hP
  subst p
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

end Certificates
end CFSG.StandardType
