module

public import CFSG.RankThree.PartOne.S10.FiveSuccessorQuasisimple
public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.TCF

open Subgroup CFSG CFSG.RankThree.PartOne
open scoped commutatorElement

@[expose] def SimpleOrBot {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  P = ⊥ ∨ (IsSimpleGroup ↥P ∧ ¬ Group.IsSolvable ↥P)

theorem simpleOrBot_bot {G : Type*} [Group G] : SimpleOrBot (⊥ : Subgroup G) := Or.inl rfl

theorem SimpleOrBot.of_mulEquiv {G H : Type*} [Group G] [Group H] {P : Subgroup G}
    {Q : Subgroup H} (e : ↥P ≃* ↥Q) (h : SimpleOrBot P) : SimpleOrBot Q := by
  rcases h with rfl | ⟨hs, hns⟩
  · left
    have : Subsingleton ↥Q := e.symm.injective.subsingleton
    exact Subgroup.eq_bot_of_subsingleton Q
  · right
    have := hs
    refine ⟨e.symm.isSimpleGroup, fun hsol => hns ?_⟩
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem SimpleOrBot.map {G H : Type*} [Group G] [Group H] {P : Subgroup G} (f : G →* H)
    (hf : Function.Injective f) (h : SimpleOrBot P) : SimpleOrBot (P.map f) :=
  h.of_mulEquiv (P.equivMapOfInjective f hf)

theorem SimpleOrBot.of_map {G H : Type*} [Group G] [Group H] {P : Subgroup G} (f : G →* H)
    (hf : Function.Injective f) (h : SimpleOrBot (P.map f)) : SimpleOrBot P :=
  h.of_mulEquiv (P.equivMapOfInjective f hf).symm

theorem simpleOrBot_of_mulEquiv_simple {G₀ G : Type*} [Group G₀] [Group G] [IsSimpleGroup G₀]
    (hns : ¬ Group.IsSolvable G₀) {P : Subgroup G} (e : G₀ ≃* ↥P) : SimpleOrBot P :=
  Or.inr ⟨e.symm.isSimpleGroup, fun _ =>
    hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)⟩

theorem simpleOrBot_range {G₀ G : Type*} [Group G₀] [Group G] [IsSimpleGroup G₀]
    (hns : ¬ Group.IsSolvable G₀) (f : G₀ →* G) (hf : Function.Injective f) :
    SimpleOrBot f.range :=
  simpleOrBot_of_mulEquiv_simple hns (MonoidHom.ofInjective hf)

theorem isQuasisimple_of_simpleOrBot {G : Type*} [Group G] {N : Subgroup G}
    (h : SimpleOrBot N) (hN : N ≠ ⊥) : CFSG.IsQuasisimple ↥N := by
  rcases h with h | ⟨hs, hns⟩
  · exact absurd h hN
  · have := hs
    have hnc : ∃ a b : ↥N, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact hns (IsSimpleGroup.comm_iff_isSolvable.1 hcon)
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

theorem component_eq_of_simpleOrBot {G : Type} [Group G] [Finite G] {C N D : Subgroup G}
    (hNC : N ≤ C) (hCN : ⁅C, C⁆ ≤ N) (hN : SimpleOrBot N) (hD : IsComponentOf C D) :
    D = N := by
  obtain ⟨hDC, hDq, hDsn⟩ := hD
  have hD1 : D ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot D).1 (CFSG.LocalCores.isQuasisimple_nontrivial hDq)
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.mp hDq.1
  have hDN : D ≤ N := by
    rw [← hDperf]
    exact (Subgroup.commutator_mono hDC hDC).trans hCN
  by_cases hN1 : N = ⊥
  · exact le_antisymm hDN (hN1 ▸ bot_le)
  · have hq := isQuasisimple_of_simpleOrBot hN hN1
    have hsn : (D.subgroupOf N).IsSubnormal := by
      have h1 := hDsn.comap (Subgroup.inclusion hNC)
      convert h1 using 1
      ext g
      simp [Subgroup.mem_subgroupOf]
    exact eq_of_isSubnormal_of_isPerfect_of_isQuasisimple hq hDN hDq.1 hD1 hsn

theorem normal_subgroupOf_of_commutator_le {G : Type*} [Group G] {C N : Subgroup G}
    (hCN : ⁅C, C⁆ ≤ N) : (N.subgroupOf C).Normal where
  conj_mem n hn g := by
    have h1 : ⁅(g : G), (n : G)⁆ ∈ N := hCN (Subgroup.commutator_mem_commutator g.2 n.2)
    have h2 : (g : G) * (n : G) * (g : G)⁻¹ = ⁅(g : G), (n : G)⁆ * (n : G) := by
      simp [commutatorElement_def]
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2]
    exact mul_mem h1 hn

theorem isComponentOf_of_simpleOrBot {G : Type} [Group G] {C N : Subgroup G} (hNC : N ≤ C)
    (hCN : ⁅C, C⁆ ≤ N) (hN : SimpleOrBot N) (hN1 : N ≠ ⊥) : IsComponentOf C N :=
  ⟨hNC, isQuasisimple_of_simpleOrBot hN hN1,
    (normal_subgroupOf_of_commutator_le hCN).isSubnormal⟩

end CFSG.RankThree.PartOne.TCF
