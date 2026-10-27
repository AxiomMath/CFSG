module

public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.RankThree.SteinbergR3ECAInnerDefiningComponentFree

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)

theorem false_of_isComponentOf {T : Type} [Group T] {X E : Subgroup T}
    (h : ∀ L : Subgroup ↥X, ¬ CFSG.IsComponent L) (hE : IsComponentOf X E) : False :=
  h (E.subgroupOf X)
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.1,
      hE.2.2⟩

theorem not_isComponent_of_isSolvable {X : Type} [Group X] [Group.IsSolvable X]
    (L : Subgroup X) : ¬ CFSG.IsComponent L := by
  intro hL
  have hs : Group.IsSolvable ↥L := inferInstance
  exact CFSG.RankThree.CAInnerDefining.not_isSolvable_of_isQuasisimple hL.1 hs

theorem centralizer_one_eq_top {T : Type} [Group T] :
    Subgroup.centralizer ({1} : Set T) = ⊤ := by
  ext g
  simp [Subgroup.mem_centralizer_singleton_iff]

@[expose] def NoCompOf (p : ℕ) (T : Type) [Group T] : Prop :=
  ∀ b : T, b ≠ 1 → b ^ p = 1 → ∀ E : Subgroup T,
    ¬ IsComponentOf (Subgroup.centralizer ({b} : Set T)) E

theorem noCompOf_of_forall {p : ℕ} {T : Type} [Group T]
    (h : ∀ b : T, b ≠ 1 → b ^ p = 1 → ∀ L : Subgroup ↥(Subgroup.centralizer ({b} : Set T)),
      ¬ CFSG.IsComponent L) : NoCompOf p T :=
  fun b hb1 hbp _ hE => false_of_isComponentOf (h b hb1 hbp) hE

theorem NoCompOf.of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : NoCompOf p T') : NoCompOf p T := by
  intro b hb1 hbp E hE
  have hE' := isComponentOf_map_mulEquiv e hE
  rw [map_centralizer_singleton_mulEquiv_good e b] at hE'
  refine h (e b) (fun h1 => hb1 (e.injective (h1.trans (map_one e).symm))) ?_ _ hE'
  rw [← map_pow, hbp, map_one]

theorem noCompOf_of_comm {p : ℕ} {T : Type} [Group T] (h : ∀ a b : T, a * b = b * a) :
    NoCompOf p T := by
  refine noCompOf_of_forall fun b _ _ L => ?_
  have : Group.IsSolvable ↥(Subgroup.centralizer ({b} : Set T)) :=
    Group.isSolvable_of_comm fun x y => Subtype.ext (h _ _)
  exact not_isComponent_of_isSolvable L

theorem innerComp_of_noCompOf {p : ℕ} {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (h : LocalRankLeTwo p T → NoCompOf p T) : InnerComp p T := by
  intro hLR b y hb _ _ E hE
  by_cases hb1 : b = 1
  · subst hb1
    rw [centralizer_one_eq_top] at hE
    have hs : IsSimpleGroup ↥(⊤ : Subgroup T) := Subgroup.topEquiv.isSimpleGroup
    have hEtop : E = ⊤ := @eq_of_isComponentOf_simple T _ ⊤ E hs hE
    rw [hEtop]
    exact Subgroup.mem_sup_left (Subgroup.mem_top y)
  · exact (h hLR b hb1 hb E hE).elim

end CFSG.RankThree.PartOne.FOCD
