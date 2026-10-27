module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem section_ten_five_actor_moved_theta_component_existence_of
    (hD6 : SectionTenFiveNormalPCoreTwoGroupWitnessFrontier) :
    SectionTenFiveActorMovedThetaComponentExistence := by
  intro G _ _ p A hS a haA ha1
  have hp := sectionTenSetup_prime hS
  have hp3 := sectionTenSetup_three_lt hS
  have hvan := sectionTenSetup_vanishing hS
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS).le
  obtain ⟨-, -, -, -, -, -, hAe, hAcard, -, -⟩ := id hS
  obtain ⟨b, hbA, hbna, Q, hQ2, hAQ, hQC, hQA, hQne, hker⟩ := hD6 G p A hS a haA ha1
  have hb1 : b ≠ 1 := fun h => hbna (h ▸ Subgroup.one_mem _)
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hAC : A ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hAe.is_comm.comm (⟨x, hx⟩ : A) ⟨b, hbA⟩)
  set A' : Subgroup C := A.subgroupOf C with hA'
  set Q' : Subgroup C := Q.subgroupOf C with hQ'
  have hmapA : A'.map C.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAC
  have hmapQ : Q'.map C.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQC
  have hevenC : evenRank C ≤ 3 := (Sec9A.evenRank_subgroup_le C).trans he
  have hA'p : IsPGroup p A' := (IsElementaryAbelian.isPGroup p A).comap_subtype
  have hA'Q' : A' ≤ normalizer (Q' : Set C) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hQ', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hAQ (Subgroup.mem_subgroupOf.mp hx)) (h : G)
  have hQA' : ⁅Q', A'⁆ = Q' := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hmapQ, hmapA]
    exact hQA
  have hθ : ⁅A', Q' ⊓ aschbacherSolvableCore p C⁆ = ⊥ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hmapA, Subgroup.map_bot,
      Subgroup.map_inf_eq _ _ C.subtype C.subtype_injective, hmapQ]
    have hAθ : A ≤ normalizer ((inSubgroup (aschbacherSolvableCore p) C : Subgroup G) : Set G) :=
      le_normalizer_theta_of_le_normalizer hp (hAC.trans Subgroup.le_normalizer)
    have h := vanishing_centralizes_invariant_two_subgroups hp hvan hAe hAcard hbA hb1
      (U := Q ⊓ inSubgroup (aschbacherSolvableCore p) C) inf_le_right
      (hQ2.to_le inf_le_left) (le_normalizer_inf_of_le_normalizer hAQ hAθ)
    rw [Subgroup.commutator_comm]
    exact h
  have haC : a ∈ C := hAC haA
  have ha' : (⟨a, haC⟩ : C) ∈ A' := Subgroup.mem_subgroupOf.mpr haA
  have hz : (Subgroup.zpowers (⟨a, haC⟩ : C)).map C.subtype = Subgroup.zpowers a := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hne : ⁅Q', Subgroup.zpowers (⟨a, haC⟩ : C)⁆ ≠ ⊥ := by
    intro h
    apply hQne
    have h2 := congrArg (Subgroup.map C.subtype) h
    rw [Subgroup.map_commutator, hmapQ, hz, Subgroup.map_bot] at h2
    exact h2
  obtain ⟨L', hL', hA'L', hcomm⟩ :=
    normal_p_core_centralizing_two_commutator_produces_theta_component ↥C hevenC p hp hp3 A' hA'p
      Q' (hQ2.comap_subtype) hA'Q' hQA' hθ hker ⟨a, haC⟩ ha' hne
  refine ⟨L'.map C.subtype,
    mem_thetaComponentFamily_iff.mpr ⟨b, hbA, hb1, ⟨L', hL', rfl⟩⟩, ?_, ?_⟩
  · intro x hx
    have hxC : x ∈ C := hAC hx
    have h1 : (⟨x, hxC⟩ : C) ∈ normalizer (L' : Set C) :=
      hA'L' (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.le_normalizer_map C.subtype ⟨⟨x, hxC⟩, h1, rfl⟩
  · rw [← hz, ← Subgroup.map_commutator, hcomm]

end CFSG.RankThree.PartOne
