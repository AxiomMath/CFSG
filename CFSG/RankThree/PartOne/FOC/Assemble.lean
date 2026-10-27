module

public import CFSG.RankThree.PartOne.FOC.InnerCase
public import CFSG.RankThree.PartOne.FOC.Transfer

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut LocalRankLeTwo LocalRankAut)

@[expose] def InnerComp (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  LocalRankLeTwo p T → ∀ b y : T, b ^ p = 1 → y ^ p = 1 → b * y = y * b →
    ∀ E : Subgroup T, IsComponentOf (Subgroup.centralizer ({b} : Set T)) E →
      y ∈ E ⊔ Subgroup.centralizer (E : Set T)

@[expose] def OuterComp (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  LocalRankLeTwo p T → ∀ β : MulAut T, β ^ p = 1 → β ∉ innerAut T → LocalRankAut p T β →
    ∀ y : T, β y = y → y ^ p = 1 → ∀ E : Subgroup T, IsComponentOf (fixSub β) E → y ∈ E

@[expose] def DefInnerComponent : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (t : StatedLieTag) (n f p : ℕ), p.Prime → 5 ≤ p →
    StatedLieAdmissible t n p f → IsSimpleGroup T → LieModel T t n p f → InnerComp p T

@[expose] def DefOuterComponent : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (t : StatedLieTag) (n f p : ℕ), p.Prime → 5 ≤ p →
    StatedLieAdmissible t n p f → IsSimpleGroup T → LieModel T t n p f → OuterComp p T

theorem fieldInnerT_of_comp {p : ℕ} {T : Type} [Group T] [Finite T]
    (hcen : Subgroup.center T = ⊥) (hin : InnerComp p T) (hout : OuterComp p T) :
    FieldInnerT p T := by
  intro hLR x β E hxp hβp hβx hβinn hE hxN hxnot hLie
  by_cases hβ : β ∈ innerAut T
  · obtain ⟨b, hb⟩ := hβ
    obtain ⟨hbp, hfix, hbx⟩ := inner_case hcen hb hβp hβx
    rw [hfix] at hE
    exact hxnot (hin hLR b x hbp hxp hbx E hE)
  · exact hxnot (Subgroup.mem_sup_left (hout hLR β hβp hβ (hβinn hβ) x hβx hxp E hE))

end CFSG.RankThree.PartOne.FOC
