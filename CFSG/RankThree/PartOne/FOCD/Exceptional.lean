module

public import CFSG.RankThree.PartOne.FOCD.Bridge
public import CFSG.LieType.Chevalley.RootLocalComponentFree
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)



theorem noCompOf_rootWeight {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (D : RootWeightDatum K) {T : Type} [Group T] (e : T ≃* D.group) : NoCompOf p T := by
  refine NoCompOf.of_mulEquiv e ?_
  intro c hc1 hcp E hE
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1
  have hQp : IsPGroup p (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hco, pow_one])
  have hQ1 : Subgroup.zpowers c ≠ ⊥ := by
    intro h
    apply hc1
    rw [← Subgroup.mem_bot, ← h]
    exact Subgroup.mem_zpowers c
  have hHc : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup D.group) : Set D.group) =
      Subgroup.centralizer ({c} : Set D.group) := by
    ext y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h g hg
      exact h g (by rw [Set.mem_singleton_iff.1 hg]; exact Subgroup.mem_zpowers c)
    · intro h g hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact (Commute.zpow_left (show Commute c y from h c rfl) k).eq
  obtain ⟨-, hcomp⟩ := D.defining_characteristic_root_local_groups_component_free p
    (Subgroup.zpowers c) hQp hQ1 (Subgroup.centralizer ({c} : Set D.group)) (Or.inr hHc.symm)
  exact false_of_isComponentOf hcomp hE

theorem noCompOf_untwisted {T : Type} [Group T] {τ : Tag} {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hm : UntwistedChevalleyModel T τ (p ^ f)) : NoCompOf p T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  exact noCompOf_rootWeight (RootWeightDatum.ordinary τ) e

theorem noCompOf_twisted {T : Type} [Group T] {t : TwistTag} {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hm : TwistedChevalleyModel T t (p ^ f)) : NoCompOf p T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card t hp hf hm
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields t hp hf K hcard
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  have hσ1 : σ ^ t.order = 1 := by
    rw [hσσ', ← hord]
    exact pow_orderOf_eq_one σ'
  have hK : Nat.card K = p ^ (f * t.order) := by rw [hcard, ← pow_mul]
  have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by have := t.order_pos; omega))) hK
  exact noCompOf_rootWeight (RootWeightDatum.fixed t σ hσ1) e

theorem noCompOf_exceptional {T : Type} [Group T] {t : StatedLieTag} {p f : ℕ} (hp : p.Prime)
    (hmod : ChevalleyExceptionalModel T t p f) : NoCompOf p T := by
  have hf : 1 ≤ f := hmod.1.2.1
  obtain ⟨-, hm⟩ := hmod
  cases t
  all_goals first
    | exact hm.elim
    | exact noCompOf_untwisted hp hf hm
    | exact noCompOf_twisted hp hf hm

end CFSG.RankThree.PartOne.FOCD
