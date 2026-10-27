module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusE7
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusLarge
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4Thm
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcF4TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import Certificates.Certificate1952

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.SeitzGeneration

theorem ggWTEx1_isWeylMatrix_E7 :
    GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan .E7)) := by
  rw [← FrameRoute.coxeterE7_eq]
  exact Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))

theorem ggWTEx1_isWeylMatrix_E8 :
    GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan .E8)) := by
  rw [← FrameRoute.coxeterE8_eq]
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)))

theorem ggWTEx1_isWeylMatrix_F4 :
    GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan .F4)) := by
  rw [← FrameRoute.coxeterF4_eq]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))))

theorem ggWTEx1_card_E7 :
    Nat.card (WeylGroup .E7) ≠ 12 := by
  rw [NoOffExc.card_weyl_E7]
  norm_num

theorem ggWTEx1_card_E8 :
    Nat.card (WeylGroup .E8) ≠ 12 := by
  rw [NoOffExc.card_weyl_E8]
  norm_num

theorem ggWTEx1_card_F4 :
    Nat.card (WeylGroup .F4) ≠ 12 := by
  have h : WeylGroup .F4 = (CoxeterMatrix.F₄).Group :=
    congrArg CoxeterMatrix.Group FrameRoute.coxeterF4_eq.symm
  rw [h, l04fFRC_ord_card_coxeterF4]
  norm_num

theorem ggWTEx1_weylTypeW_E7Plus_threeFive
    {p : ℕ} (hp35 : p = 3 ∨ p = 5) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusWeylTypeW p 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  exact ggWTEx1_weylTypeW_of_excPlusModel hp hp2 ggWTEx1_isWeylMatrix_E7 ggWTEx1_card_E7
    (ggExcPlusWeylModelSCr_of_frameModel (Or.inl rfl) hp hp2 K
      (excPlusFrameModel_E7_threeFive hp35 K hpq))

theorem ggWTEx1_weylTypeW_E8Plus_threeFive
    {p : ℕ} (hp35 : p = 3 ∨ p = 5) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusWeylTypeW p 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  exact ggWTEx1_weylTypeW_of_excPlusModel hp hp2 ggWTEx1_isWeylMatrix_E8 ggWTEx1_card_E8
    (ggExcPlusWeylModelSCr_of_frameModel (Or.inr rfl) hp hp2 K
      (excPlusFrameModel_E8_threeFive hp35 K hpq))

theorem ggWTEx1_weylTypeW_E7Plus_large
    {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusWeylTypeW p 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  have hp2 : p ≠ 2 := by omega
  exact ggWTEx1_weylTypeW_of_excPlusModel hp hp2 ggWTEx1_isWeylMatrix_E7 ggWTEx1_card_E7
    (ggExcPlusWeylModelSCr_of_frameModel (Or.inl rfl) hp hp2 K
      (excPlusFrameModel_large (Or.inl rfl) hp h11 K hpq fun Fr hFr X hX hXC hXF => by
        haveI := hX
        exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF))

theorem ggWTEx1_weylTypeW_E8Plus_large
    {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusWeylTypeW p 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have hp2 : p ≠ 2 := by omega
  refine ggWTEx1_weylTypeW_of_excPlusModel hp hp2 ggWTEx1_isWeylMatrix_E8 ggWTEx1_card_E8
    (ggExcPlusWeylModelSCr_of_frameModel (Or.inr rfl) hp hp2 K
      (excPlusFrameModel_large (Or.inr rfl) hp h11 K hpq fun Fr hFr X hX hXC hXF => ?_))
  haveI := hX
  exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1
    (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
      (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1)

theorem ggWTEx1_weylTypeW_F4_four
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (K : Type) [Field K] [Finite K] [CharP K 2] :
    GGTorusWeylTypeW p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  have hF : GGTorusWeylFrameW p 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)
      CoxeterMatrix.F₄ :=
    ggTorusWeylFrameW_of_coordFrameElt hp hp2
      (TableBF4.idImage_subset_inn K) (TableBF4.center_recipeGroup_eq_bot K)
      (ggTorusWeylGenElt_of_mulEquiv (TableBF4.recipeEquiv K)
        (ExcWeylGen.ggTorusWeylGenElt_adjointF4_all hp hp2))
      (ggTorusCoordFrameElt_of_mulEquiv (TableBF4.recipeEquiv K)
        (ggWTF4_coordFrameElt_adjointF4 (K := K) hp hp2))
  exact ggWTF4_weylTypeW_of_frame (M := CoxeterMatrix.F₄)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)))))
    (by rw [l04fFRC_ord_card_coxeterF4]; norm_num) hF

theorem ggWTEx1_weylTypeW_F4Plus_of_four
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusWeylTypeW p 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) := by
  have hp2 : p ≠ 2 := by omega
  have := TableBF4.finite_recipeGroup (K := K)
  have he := ExcFramesHalf.orderOf_eq_two_of_dvd_add_one hp hp2 hpq
  have hT : SylowTorus (TableBF4.RecipeGroup K) p 4 :=
    (OrdPInnerExc.sylowTorus_F4_two K hp hp3 he).of_mulEquiv (TableBF4.recipeEquiv K).symm
  refine ggWTEx1_weylTypeW_of_selfCent_card hp (TableBF4.center_recipeGroup_eq_bot K)
    (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ) (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2)
    (fun E hE _ hsc => ?_) (ggWTEx1_weylTypeW_F4_four hp hp2 K)
  rw [card_eq_of_selfCentralizing_of_sylowTorus hp hT hE hsc]

end CFSG.StandardType

end
