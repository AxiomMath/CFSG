module

public import CFSG.OddTranspositions.HalphaThreeTranspositions
public import CFSG.Fischer.Classification.Basic.Trichotomy

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Connectivity CFSG.Fischer
open CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem reach_imp_commGraph_reachable {x y : D}
    (h : Reach D (x : G) (y : G)) : (commGraph D).Reachable x y := by
  have key : ∀ {a : G}, Reach D a (y : G) → ∀ ha : a ∈ D,
      (commGraph D).Reachable ⟨a, ha⟩ y := by
    intro a hpath
    refine Relation.ReflTransGen.head_induction_on hpath ?_ ?_
    · intro ha
      have hya : (⟨(y : G), ha⟩ : D) = y := Subtype.ext rfl
      rw [hya]
    · intro a' c hstep _ ih ha
      by_cases hEq : (⟨a', ha⟩ : D) = ⟨c, hstep.2.1⟩
      · rw [hEq]
        exact ih hstep.2.1
      · exact ((show (commGraph D).Adj ⟨a', ha⟩ ⟨c, hstep.2.1⟩ from
          ⟨hEq, hstep.2.2⟩)).reachable.trans (ih hstep.2.1)
  simpa using key h x.2

theorem commGraph_reachable_imp_reach {x y : D}
    (h : (commGraph D).Reachable x y) : Reach D (x : G) (y : G) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  exact h.lift Subtype.val (fun a b hab => ⟨a.2, b.2, hab.2⟩)

theorem reach_iff_commGraph_reachable {x y : D} :
    Reach D (x : G) (y : G) ↔ (commGraph D).Reachable x y :=
  ⟨reach_imp_commGraph_reachable, commGraph_reachable_imp_reach⟩

theorem commGraph_connected_of_not_disconnected (hne : D.Nonempty)
    (h : ¬ Disconnected D) : (commGraph D).Connected := by
  obtain ⟨x, hx⟩ := hne
  refine (SimpleGraph.connected_iff_exists_forall_reachable (commGraph D)).2 ⟨⟨x, hx⟩, ?_⟩
  intro y
  exact (reach_iff_commGraph_reachable (D := D)).1 (reach_of_not_disconnected h hx y.2)

theorem center_quotient_H_eq_bot (hC : HypothesisC D) :
    Subgroup.center (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ :=
  center_eq_bot_of_solvableRadical_eq_bot (solvableRadical_quotient_H hC)

theorem no_normal_two_H (hC : HypothesisC D) :
    ∀ N : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hP
  exact eq_bot_of_normal_isPGroup_of_solvableRadical_eq_bot Nat.prime_two hN hP
    (solvableRadical_quotient_H hC)

theorem no_normal_three_H (hC : HypothesisC D) :
    ∀ N : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      N.Normal → IsPGroup 3 N → N = ⊥ := by
  intro N hN hP
  exact eq_bot_of_normal_isPGroup_of_solvableRadical_eq_bot Nat.prime_three hN hP
    (solvableRadical_quotient_H hC)

theorem commutator_simple_imageClass (hC : HypothesisC D)
    (hQ : Config D u w v z a K₁ S') (hmin : SmallerTwoStar (Nat.card G))
    (hconn : ¬ Disconnected (imageClass hC))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha)) :
    IsSimpleGroup (commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :=
  CFSG.Fischer.Classification.Pair.isSimpleGroup_commutator_of_connected
    (fischerPair_imageClass hC hQ hmin hconn hHns)
    (center_quotient_H_eq_bot hC) (no_normal_two_H hC) (no_normal_three_H hC)
    (commGraph_connected_of_not_disconnected (imageClass_nonempty hC) hconn)

end CFSG.OddTranspositions
