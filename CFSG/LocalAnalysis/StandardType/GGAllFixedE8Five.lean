module

public import CFSG.LocalAnalysis.StandardType.GGAllFixedA8Seven
public import CFSG.LocalAnalysis.StandardType.GGAllFixedExceptionalToral
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE8Three
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FivePositioning
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate13720
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064

public section


namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open CFSG.StandardType.ExcFramesHalf
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
open scoped commutatorElement

private theorem hasNormalPComplement_commutator_of_mulEquiv
    {G H : Type} [Group G] [Group H] {p : ℕ} (e : G ≃* H)
    (h : CFSG.HasNormalPComplement p ↥(_root_.commutator G)) :
    CFSG.HasNormalPComplement p ↥(_root_.commutator H) := by
  have hmap : (_root_.commutator G).map e.toMonoidHom = _root_.commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective,
      ← _root_.commutator_def]
  let eD : ↥(_root_.commutator G) ≃* ↥(_root_.commutator H) :=
    ((_root_.commutator G).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact CFSG.hasNormalPComplement_of_equiv p eD h

section Certificates


theorem e8_five_adjoint_full_centralizer_solvable
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h5 : 5 ∣ Nat.card K ^ 2 - 1)
    (A : Subgroup (adjointGroup Tag.E8 K))
    (hA : IsElemAbelian 5 A) (hcard : 5 ^ 3 ≤ Nat.card A)
    (hNPC : CFSG.HasNormalPComplement 5
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup Tag.E8 K))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup Tag.E8 K))) := by
  classical
  let L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Finite (adjointGroup Tag.E8 K) := by
    have : Finite (ModGL Tag.E8 K) := finite_modGL
    exact Subtype.finite
  have : Finite A := Subtype.finite
  by_cases hT : IsToralSubgroup Tag.E8 L
      (A.map ((baseChangeGL (algebraMap K L)).comp (adjointGroup Tag.E8 K).subtype))
  · exact adjoint_full_toral_centralizer_solvable
      (Or.inr (Or.inr (Or.inr rfl))) Nat.prime_five (by decide) h5 A hA.2 hT hNPC
  · have hCeq :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five.centralizer_eq_of_nonToral_baseChange
        (f := algebraMap K L) A hA hT hcard
    rw [hCeq]
    have : IsMulCommutative A := hA.1
    infer_instance

theorem ggFixedSubgroup_isSolvable_of_recipe_E8Five
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h5 : 5 ∣ Nat.card K ^ 2 - 1)
    (E : Subgroup (MulAut (TableBExc.RecipeGroup .E8 K)))
    (hEI : (E : Set (MulAut (TableBExc.RecipeGroup .E8 K))) ⊆ TableBExc.RecipeID .E8 K)
    (hE : IsElemAbelian 5 E) (hcard : 5 ^ 3 ≤ Nat.card E)
    (hNPC : CFSG.HasNormalPComplement 5
      ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have hinner : E ≤ (MulAut.conj : TableBExc.RecipeGroup .E8 K →*
      MulAut (TableBExc.RecipeGroup .E8 K)).range := fun a ha =>
    TableBExc.idImage_subset_inn_E8 K (hEI ha)
  let eR := TableBExc.recipeEquiv .E8 K
  let E' : Subgroup (MulAut (adjointGroup .E8 K)) := E.map (MulAut.congr eR).toMonoidHom
  have hE'range : E' ≤ (MulAut.conj : adjointGroup .E8 K →*
      MulAut (adjointGroup .E8 K)).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg⟩ := hinner ha
    refine ⟨eR g, ?_⟩
    rw [← hg]
    exact (mulAut_congr_conj eR g).symm
  let A : Subgroup (adjointGroup .E8 K) := E'.comap (MulAut.conj :
    adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))
  have hconj : Function.Injective (MulAut.conj : adjointGroup .E8 K →*
      MulAut (adjointGroup .E8 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hAmap : A.map (MulAut.conj : adjointGroup .E8 K →*
      MulAut (adjointGroup .E8 K)) = E' := Subgroup.map_comap_eq_self hE'range
  have hA : IsElemAbelian 5 A := (hE.map (MulAut.congr eR).toMonoidHom).comap hconj
  have hAcard : 5 ^ 3 ≤ Nat.card A := by
    have h1 : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.congr eR).injective
    have h2 : Nat.card A = Nat.card E' := by
      rw [← hAmap]
      exact (Subgroup.card_map_of_injective hconj).symm
    rwa [h2, h1]
  have hfix : ggFixedSubgroup E' =
      Subgroup.centralizer (A : Set (adjointGroup .E8 K)) := by
    rw [← hAmap, ggFixedSubgroup_map_conj_eq_centralizer]
  have hmapFix : ggFixedSubgroup E' = (ggFixedSubgroup E).map eR.toMonoidHom :=
    ggFixedSubgroup_map_congr eR E
  let eF : ↥(ggFixedSubgroup E) ≃* ↥(ggFixedSubgroup E') :=
    ((ggFixedSubgroup E).equivMapOfInjective eR.toMonoidHom eR.injective).trans
      (MulEquiv.subgroupCongr hmapFix.symm)
  let C : Subgroup (adjointGroup .E8 K) :=
    Subgroup.centralizer (A : Set (adjointGroup .E8 K))
  let eC : ↥(ggFixedSubgroup E) ≃* ↥C :=
    eF.trans (MulEquiv.subgroupCongr hfix)
  have hNPC_C : CFSG.HasNormalPComplement 5 ↥(_root_.commutator ↥C) :=
    hasNormalPComplement_commutator_of_mulEquiv eC hNPC
  have hsolvC : Group.IsSolvable ↥C :=
    e8_five_adjoint_full_centralizer_solvable (K := K) h5 A hA hAcard hNPC_C
  have hsolvE' : Group.IsSolvable ↥(ggFixedSubgroup E') := by
    rw [hfix]
    exact hsolvC
  have : Group.IsSolvable ↥((ggFixedSubgroup E).map eR.toMonoidHom) := by
    rw [← hmapFix]
    exact hsolvE'
  exact Group.isSolvable_of_isSolvable_injective
    (f := eR.toMonoidHom.subgroupMap (ggFixedSubgroup E))
    (MonoidHom.subgroupMap_injective eR.toMonoidHom _ eR.injective)

theorem largeEvenLabelAll_E8Five_fullFixedSolvable
    {n : ℕ} (h5 : 5 ∣ (2 ^ n) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.E8, 0, n⟩ fun R _ I _ =>
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian 5 E → 5 ^ 3 ≤ Nat.card E →
        CFSG.HasNormalPComplement 5 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  change LargeEvenRecipeChevalley (LargeEvenCartanE 8) (2 ^ n) false Q at hQ
  refine recipeChevalley_and (P := fun R _ I _ =>
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
      IsElemAbelian 5 E → 5 ^ 3 ≤ Nat.card E →
      CFSG.HasNormalPComplement 5 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E)) ?_ hQ
  intro K _ _ hK E hEI hE hcard hNPC
  have : CharP K 2 := charP_two_of_card hK
  have h5K : 5 ∣ Nat.card K ^ 2 - 1 := by
    rw [hK]
    exact h5
  exact ggFixedSubgroup_isSolvable_of_recipe_E8Five (K := K) h5K E hEI hE hcard hNPC

theorem isSolvable_inf_centralizer_of_E8Five_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      lab.tag = .E8 ∧ lab.rank = 0 ∧ p = 5 ∧ 5 ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian 5 (ggBeta (G := G) (L := X) θ hN).range ∧
        5 ^ 3 ≤ Nat.card (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .E8 ∧ lab.rank = 0 ∧ p = 5 ∧
      5 ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R),
      (E : Set (MulAut R)) ⊆ I → IsElemAbelian 5 E → 5 ^ 3 ≤ Nat.card E →
      CFSG.HasNormalPComplement 5 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab hlab hs => by
      obtain ⟨htag, hrank, -, h5n⟩ := hs
      cases lab with
      | mk tag rank n =>
        cases htag
        cases hrank
        exact largeEvenLabelAll_E8Five_fullFixedSolvable (n := n) h5n)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) hmark
  obtain ⟨lab, hlab, hhas, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hp5, -, hN, hEI, hE, hcard⟩, hrow⟩ := hP
  subst p
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE hcard
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

theorem e8_three_adjoint_full_centralizer_solvable
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K ^ 2 - 1)
    (A : Subgroup (adjointGroup Tag.E8 K))
    (hA : IsElemAbelian 3 A) (hcard : 3 ^ 7 ≤ Nat.card A)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(Subgroup.centralizer (A : Set (adjointGroup Tag.E8 K))))) :
    Group.IsSolvable ↥(Subgroup.centralizer (A : Set (adjointGroup Tag.E8 K))) := by
  have hT : IsToralSubgroup Tag.E8 (AlgebraicClosure K)
      (A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E8 K).subtype)) := by
    by_contra hNT
    exact absurd hcard (not_le.mpr (E8ThreeWNorm.card_lt_of_nonToral A hA hNT))
  exact adjoint_full_toral_centralizer_solvable
    (Or.inr (Or.inr (Or.inr rfl))) Nat.prime_three (by decide) h3 A hA.2 hT hNPC

theorem ggFixedSubgroup_isSolvable_of_recipe_E8Three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K ^ 2 - 1)
    (E : Subgroup (MulAut (TableBExc.RecipeGroup .E8 K)))
    (hEI : (E : Set (MulAut (TableBExc.RecipeGroup .E8 K))) ⊆ TableBExc.RecipeID .E8 K)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 7 ≤ Nat.card E)
    (hNPC : CFSG.HasNormalPComplement 3
      ↥(_root_.commutator ↥(ggFixedSubgroup E))) :
    Group.IsSolvable ↥(ggFixedSubgroup E) := by
  classical
  have hinner : E ≤ (MulAut.conj : TableBExc.RecipeGroup .E8 K →*
      MulAut (TableBExc.RecipeGroup .E8 K)).range := fun a ha =>
    TableBExc.idImage_subset_inn_E8 K (hEI ha)
  let eR := TableBExc.recipeEquiv .E8 K
  let E' : Subgroup (MulAut (adjointGroup .E8 K)) := E.map (MulAut.congr eR).toMonoidHom
  have hE'range : E' ≤ (MulAut.conj : adjointGroup .E8 K →*
      MulAut (adjointGroup .E8 K)).range := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨g, hg⟩ := hinner ha
    refine ⟨eR g, ?_⟩
    rw [← hg]
    exact (mulAut_congr_conj eR g).symm
  let A : Subgroup (adjointGroup .E8 K) := E'.comap (MulAut.conj :
    adjointGroup .E8 K →* MulAut (adjointGroup .E8 K))
  have hconj : Function.Injective (MulAut.conj : adjointGroup .E8 K →*
      MulAut (adjointGroup .E8 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hAmap : A.map (MulAut.conj : adjointGroup .E8 K →*
      MulAut (adjointGroup .E8 K)) = E' := Subgroup.map_comap_eq_self hE'range
  have hA : IsElemAbelian 3 A := (hE.map (MulAut.congr eR).toMonoidHom).comap hconj
  have hAcard : 3 ^ 7 ≤ Nat.card A := by
    have h1 : Nat.card E' = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.congr eR).injective
    have h2 : Nat.card A = Nat.card E' := by
      rw [← hAmap]
      exact (Subgroup.card_map_of_injective hconj).symm
    rwa [h2, h1]
  have hfix : ggFixedSubgroup E' =
      Subgroup.centralizer (A : Set (adjointGroup .E8 K)) := by
    rw [← hAmap, ggFixedSubgroup_map_conj_eq_centralizer]
  have hmapFix : ggFixedSubgroup E' = (ggFixedSubgroup E).map eR.toMonoidHom :=
    ggFixedSubgroup_map_congr eR E
  let eF : ↥(ggFixedSubgroup E) ≃* ↥(ggFixedSubgroup E') :=
    ((ggFixedSubgroup E).equivMapOfInjective eR.toMonoidHom eR.injective).trans
      (MulEquiv.subgroupCongr hmapFix.symm)
  let C : Subgroup (adjointGroup .E8 K) :=
    Subgroup.centralizer (A : Set (adjointGroup .E8 K))
  let eC : ↥(ggFixedSubgroup E) ≃* ↥C :=
    eF.trans (MulEquiv.subgroupCongr hfix)
  have hNPC_C : CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥C) :=
    hasNormalPComplement_commutator_of_mulEquiv eC hNPC
  have hsolvC : Group.IsSolvable ↥C :=
    e8_three_adjoint_full_centralizer_solvable (K := K) h3 A hA hAcard hNPC_C
  have hsolvE' : Group.IsSolvable ↥(ggFixedSubgroup E') := by
    rw [hfix]
    exact hsolvC
  have : Group.IsSolvable ↥((ggFixedSubgroup E).map eR.toMonoidHom) := by
    rw [← hmapFix]
    exact hsolvE'
  exact Group.isSolvable_of_isSolvable_injective
    (f := eR.toMonoidHom.subgroupMap (ggFixedSubgroup E))
    (MonoidHom.subgroupMap_injective eR.toMonoidHom _ eR.injective)

theorem largeEvenLabelAll_E8Three_lift_and_fullFixedSolvable {n : ℕ}
    (h3 : 3 ∣ (2 ^ n) ^ 2 - 1) :
    LargeEvenLabelAll ⟨.E8, 0, n⟩ fun R _ I _ =>
      GGTorusLift 3 7 R ∧
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian 3 E → 3 ^ 7 ≤ Nat.card E →
        CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E) := by
  intro Q hQ
  change LargeEvenRecipeChevalley (LargeEvenCartanE 8) (2 ^ n) false Q at hQ
  refine recipeChevalley_and (P := fun R _ I _ =>
    GGTorusLift 3 7 R ∧
    ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
      IsElemAbelian 3 E → 3 ^ 7 ≤ Nat.card E →
      CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
      Group.IsSolvable ↥(ggFixedSubgroup E)) ?_ hQ
  intro K _ _ hK
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨E8ThreeWNorm.ggTorusLift_E8_three_seven, ?_⟩
  intro E hEI hE hcard hNPC
  apply ggFixedSubgroup_isSolvable_of_recipe_E8Three (K := K) ?_ E hEI hE hcard hNPC
  rwa [hK]

theorem isSolvable_inf_centralizer_of_E8Three_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hmark : LargeEvenMarking ↥X fun lab R _ I _ θ =>
      lab.tag = .E8 ∧ lab.rank = 0 ∧ p = 3 ∧ 3 ∣ (2 ^ lab.n) ^ 2 - 1 ∧
      ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
        ((ggBeta (G := G) (L := X) θ hN).range : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian 3 (ggBeta (G := G) (L := X) θ hN).range) :
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Bs : Set G)) := by
  have hcombined := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .E8 ∧ lab.rank = 0 ∧ p = 3 ∧
      3 ∣ (2 ^ lab.n) ^ 2 - 1)
    (P' := fun R _ I _ => GGTorusLift 3 7 R ∧
      ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian 3 E → 3 ^ 7 ≤ Nat.card E →
        CFSG.HasNormalPComplement 3 ↥(_root_.commutator ↥(ggFixedSubgroup E)) →
        Group.IsSolvable ↥(ggFixedSubgroup E))
    (fun lab _ hs => by
      obtain ⟨htag, hrank, -, h3n⟩ := hs
      cases lab with
      | mk tag rank n =>
        cases htag
        cases hrank
        exact largeEvenLabelAll_E8Three_lift_and_fullFixedSolvable (n := n) h3n)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) hmark
  obtain ⟨lab, _, _, R, _, I, _, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcombined
  obtain ⟨⟨-, -, hp3, -, hN, hEI, hE⟩, hlift, hrow⟩ := hP
  subst p
  have hcard := pow_le_card_ggBeta_of_torusLift_of_ggConfig hcfg hX θ hN hmark.1 hlift
  have hsolv := hrow (ggBeta (G := G) (L := X) θ hN).range hEI hE hcard
    (hasNormalPComplement_commutator_ggFixedSubgroup_of_ggConfig hcfg hN θ)
  exact isSolvable_inf_centralizer_of_quotientFixed_solvable hN θ hsolv

end Certificates
