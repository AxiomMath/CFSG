module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.Adapters.WholeGroupLayer

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

theorem signalizerGeneralizedFitting_eq (X : Type*) [Group X] :
    signalizerGeneralizedFitting X = CFSG.generalizedFitting X :=
  CFSG.Adapters.signalizerGeneralizedFitting_eq_foundations X

@[expose] def IsFStarSimple (X : Type*) [Group X] : Prop :=
  IsSimpleGroup (CFSG.generalizedFitting X) ∧ ¬ IsMulCommutative (CFSG.generalizedFitting X)

theorem nonempty_mulEquiv_generalizedFitting {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nonempty (↥(CFSG.generalizedFitting X) ≃* ↥(CFSG.generalizedFitting Y)) := by
  obtain ⟨ε⟩ := CFSG.SignalizerFunctorTheorem.TransportA.nonempty_mulEquiv_generalizedFitting e
  exact ⟨(MulEquiv.subgroupCongr (signalizerGeneralizedFitting_eq X).symm).trans
    (ε.trans (MulEquiv.subgroupCongr (signalizerGeneralizedFitting_eq Y)))⟩

theorem isFStarSimple_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    IsFStarSimple X ↔ IsFStarSimple Y := by
  obtain ⟨ε⟩ := nonempty_mulEquiv_generalizedFitting e
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨ε.symm.isSimpleGroup, fun h => h2 ((isMulCommutative_congr ε).mpr h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨ε.isSimpleGroup, fun h => h2 ((isMulCommutative_congr ε).mp h)⟩

theorem isFStarSimple_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hnc : ¬ IsMulCommutative S) : IsFStarSimple S := by
  have hnonab : ∃ a b : S, a * b ≠ b * a := by
    simpa only [isMulCommutative_iff, not_forall] using hnc
  have hlayer : CFSG.layer S = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Unit) (S := fun _ => S) (fun _ => hnonab)
      (MulEquiv.funUnique Unit S).symm
  have htop : CFSG.generalizedFitting S = ⊤ := by
    rw [CFSG.generalizedFitting, hlayer, sup_top_eq]
  rw [IsFStarSimple, htop]
  exact ⟨Subgroup.topEquiv.isSimpleGroup, fun h => hnc ((isMulCommutative_congr
    (Subgroup.topEquiv (G := S))).mp h)⟩

theorem normal_generalizedFitting (X : Type*) [Group X] : (CFSG.generalizedFitting X).Normal := by
  rw [CFSG.generalizedFitting_eq_componentClassification]
  exact CFSG.ComponentClassification.GeneralizedFitting.normal X

theorem isFStarSimple_iff_inSubgroup {Γ : Type*} [Group Γ] (C : Subgroup Γ) :
    IsFStarSimple ↥C ↔ IsSimpleGroup ↥(CFSG.inSubgroup CFSG.generalizedFitting C) ∧
      ¬ IsMulCommutative ↥(CFSG.inSubgroup CFSG.generalizedFitting C) := by
  let e : ↥(CFSG.generalizedFitting ↥C) ≃* ↥(CFSG.inSubgroup CFSG.generalizedFitting C) :=
    Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨e.symm.isSimpleGroup, fun h => h2 ((isMulCommutative_congr e).mpr h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e.isSimpleGroup, fun h => h2 ((isMulCommutative_congr e).mp h)⟩

theorem normal_inSubgroup_generalizedFitting {Γ : Type*} [Group Γ] (C : Subgroup Γ) :
    ((CFSG.inSubgroup CFSG.generalizedFitting C).subgroupOf C).Normal := by
  have h : (CFSG.inSubgroup CFSG.generalizedFitting C).subgroupOf C =
      CFSG.generalizedFitting ↥C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  rw [h]
  exact normal_generalizedFitting _

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
