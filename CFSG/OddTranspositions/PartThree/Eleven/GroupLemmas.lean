module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic

import CFSG.Quasithin.Recognition.M12AscTrans
import Mathlib.Tactic.Group

public section

namespace CFSG.OddTranspositions.PartThree

open scoped commutatorElement

private theorem s11g_isPGroup_zpowers_of_mul_self {X : Type*} [Group X] {a : X}
    (ha : a * a = 1) : IsPGroup 2 (Subgroup.zpowers a) := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem le_commutator_of_index_commutator_quotient {X : Type*} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal] (hX : (commutator X).index ≤ 2)
    (hQ : (commutator (X ⧸ N)).index = 2) : N ≤ commutator X := by
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hmap : (commutator X).map π = commutator (X ⧸ N) := by
    simp only [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hsurj]
  have hcomap : (commutator (X ⧸ N)).comap π = commutator X ⊔ N := by
    rw [← hmap, Subgroup.comap_map_eq, hker]
  have hKindex : (commutator X ⊔ N).index = 2 := by
    rw [← hcomap]
    rw [Subgroup.index_comap_of_surjective (commutator (X ⧸ N)) hsurj]
    exact hQ
  have h2dvd : 2 ∣ (commutator X).index := by
    have hdvd : (commutator X ⊔ N).index ∣ (commutator X).index :=
      Subgroup.index_dvd_of_le le_sup_left
    rwa [hKindex] at hdvd
  have hne : (commutator X).index ≠ 0 :=
    (inferInstance : (commutator X).FiniteIndex).index_ne_zero
  have hHindex : (commutator X).index = 2 :=
    le_antisymm hX (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h2dvd)
  have hHK : (commutator X) = commutator X ⊔ N :=
    Subgroup.eq_of_index_dvd_index le_sup_left
      (by rw [hHindex, hKindex])
  rw [hHK]
  exact le_sup_right

theorem commute_of_closure_isConj_of_commutator_le_center {X : Type*} [Group X] (d₀ : X)
    (hgen : Subgroup.closure {g : X | IsConj d₀ g} = ⊤)
    (h : commutator X ≤ Subgroup.center X) (a b : X) : Commute a b := by
  have hcent : ∀ g : X, IsConj d₀ g → ∃ z ∈ Subgroup.center X, g = d₀ * z := by
    intro g hg
    rw [isConj_iff] at hg
    obtain ⟨c, hc⟩ := hg
    refine ⟨d₀⁻¹ * c * d₀ * c⁻¹, ?_, ?_⟩
    · apply h
      have hmem : ⁅d₀⁻¹, c⁆ ∈ commutator X := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      simpa [commutatorElement_def] using hmem
    · rw [← hc]
      group
  have hpair : Set.Pairwise {g : X | IsConj d₀ g} Commute := by
    intro g hg g' hg' _
    obtain ⟨z, hz, rfl⟩ := hcent g hg
    obtain ⟨z', hz', rfl⟩ := hcent g' hg'
    have hcz : ∀ x : X, Commute x z := fun x =>
      (commute_iff_eq x z).mpr (Subgroup.mem_center_iff.mp hz x)
    have hcz' : ∀ x : X, Commute x z' := fun x =>
      (commute_iff_eq x z').mpr (Subgroup.mem_center_iff.mp hz' x)
    exact Commute.mul_left (Commute.mul_right (Commute.refl d₀) (hcz' d₀))
      (Commute.mul_right (hcz d₀).symm (hcz' z))
  haveI : IsMulCommutative (Subgroup.closure {g : X | IsConj d₀ g}) :=
    Subgroup.isMulCommutative_closure hpair
  have ha : a ∈ Subgroup.closure {g : X | IsConj d₀ g} := by rw [hgen]; trivial
  have hb : b ∈ Subgroup.closure {g : X | IsConj d₀ g} := by rw [hgen]; trivial
  have hcomm := mul_comm'
    (⟨a, ha⟩ : Subgroup.closure {g : X | IsConj d₀ g}) ⟨b, hb⟩
  exact congrArg Subtype.val hcomm

theorem false_of_transfer {X : Type*} [Group X] [Finite X] (d₀ : X) (hd₀ : d₀ * d₀ = 1)
    (hgen : Subgroup.closure {g : X | IsConj d₀ g} = ⊤) (S : Sylow 2 X) {Q : Subgroup X}
    (hQS : Q ≤ S) (hindex : Q.relIndex (S : Subgroup X) = 2)
    (hSD : ∀ g ∈ (S : Subgroup X), IsConj d₀ g → g ∈ Q)
    {x : X} (hx : x * x = 1) (hxS : x ∈ (S : Subgroup X)) (hxQ : ∀ a : X, a⁻¹ * x * a ∉ Q) :
    False := by
  obtain ⟨X₀, hX₀n, hX₀i, hxX₀, hcrit⟩ :=
    CFSG.Quasithin.thompson_transfer_index_two S hindex hx hxS hxQ
  have hmem : ∀ g ∈ (S : Subgroup X), IsConj d₀ g → g ∈ X₀ := by
    intro g hgS hg
    have hg2 : g * g = 1 := by
      have h2 : IsConj (g * g) (d₀ * d₀) := by
        simpa only [pow_two] using hg.symm.pow 2
      rw [hd₀] at h2
      exact isConj_one_left.mp h2
    refine (hcrit g hgS hg2 ?_).mpr (hSD g hgS hg)
    intro a ha
    refine ⟨fun _ => hSD g hgS hg, fun _ => hSD (a⁻¹ * g * a) ha ?_⟩
    exact hg.trans (isConj_iff.mpr ⟨a⁻¹, by rw [inv_inv]⟩)
  obtain ⟨a, ha⟩ : ∃ a : X, a⁻¹ * d₀ * a ∈ (S : Subgroup X) := by
    have hP : IsPGroup 2 (Subgroup.zpowers d₀) := s11g_isPGroup_zpowers_of_mul_self hd₀
    obtain ⟨Q₀, hQ₀⟩ := hP.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q₀ S
    refine ⟨g⁻¹, ?_⟩
    have hd₀Q₀ : d₀ ∈ (Q₀ : Subgroup X) := hQ₀ (Subgroup.mem_zpowers d₀)
    have hmem' : g * d₀ * g⁻¹ ∈ ((g • Q₀ : Sylow 2 X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul d₀ (MulAut.conj g) (Q₀ : Subgroup X) hd₀Q₀
    rw [hg] at hmem'
    simpa [inv_inv] using hmem'
  have hconjX₀ : a⁻¹ * d₀ * a ∈ X₀ :=
    hmem _ ha (isConj_iff.mpr ⟨a⁻¹, by rw [inv_inv]⟩)
  have hd₀X₀ : d₀ ∈ X₀ := by
    have hconj := hX₀n.conj_mem (a⁻¹ * d₀ * a) hconjX₀ a
    rwa [show a * (a⁻¹ * d₀ * a) * a⁻¹ = d₀ from by group] at hconj
  have htop : (⊤ : Subgroup X) ≤ X₀ := by
    rw [← hgen, Subgroup.closure_le]
    intro g hg
    change IsConj d₀ g at hg
    rw [isConj_iff] at hg
    obtain ⟨c, hc⟩ := hg
    rw [← hc]
    exact hX₀n.conj_mem d₀ hd₀X₀ c
  have hX₀top : X₀ = ⊤ := top_le_iff.mp htop
  rw [hX₀top, Subgroup.index_top] at hX₀i
  exact absurd hX₀i (by decide)

end CFSG.OddTranspositions.PartThree
