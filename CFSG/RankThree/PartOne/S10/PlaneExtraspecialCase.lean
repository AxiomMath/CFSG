module

public import CFSG.RankThree.PartOne.S10.PlaneFactorCases
import CFSG.RankThree.PartOne.S10.PlaneCoreBounds
import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
import CFSG.RankThree.GroupTheory.SteinbergBMClassTwoExtraspecialAction

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly
open scoped commutatorElement

namespace PlaneExtraspecialCase

theorem zpowers_eq_of_card_two {G : Type*} [Group G] {H : Subgroup G} (hH : Nat.card H = 2) {z : G}
    (hz : z ∈ H) (hz1 : z ≠ 1) : Subgroup.zpowers z = H := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
  rw [hH, Nat.card_zpowers]
  have h2 : orderOf z ∣ 2 := by
    have := orderOf_dvd_natCard (⟨z, hz⟩ : H)
    rwa [hH, Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hz1
  · exact h.ge

theorem extraspecial_case_contradiction {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {B S D : Type}
    [Group B] [Group S] [Group D] [Finite B] [Finite S] [Finite D] [MulDistribMulAction B S]
    (hS : IsPGroup 2 S) (hDp : IsPGroup p D) (hDexp : ∀ x : D, x ^ p = 1)
    (hDcl : commutator D ≤ Subgroup.center D)
    (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D) (hβ : Function.Injective β)
    (he : evenRank (D ⋊[β] (S ⋊[MulDistribMulAction.toMulAut B S] B)) ≤ 3)
    {S₁ S₂ Z₁ Z₂ : Subgroup S} {n₁ n₂ : ℕ}
    (hsp₁ : PlaneFactorCases.SpecialData (B := B) S₁ Z₁ n₁)
    (hsp₂ : PlaneFactorCases.SpecialData (B := B) S₂ Z₂ n₂)
    (hcomm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) (hZ : Nat.card (Z₁ ⊔ Z₂ : Subgroup S) = 2) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Z₁ ⊔ Z₂ with hZdef
  have hZfin : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hsubZ : ∀ W : Subgroup S, W ≤ Z → W ≠ ⊥ → W = Z := by
    intro W hWZ hW
    obtain ⟨⟨w, hw⟩, hw1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
    have hw1 : w ≠ 1 := fun h => hw1' (Subtype.ext h)
    have h1 : Subgroup.zpowers w = Z := zpowers_eq_of_card_two hZ (hWZ hw) hw1
    exact le_antisymm hWZ (calc Z = Subgroup.zpowers w := h1.symm
      _ ≤ W := Subgroup.zpowers_le.mpr hw)
  have hZ₁ : Z₁ = Z := hsubZ Z₁ le_sup_left hsp₁.ne_bot
  have hZ₂ : Z₂ = Z := hsubZ Z₂ le_sup_right hsp₂.ne_bot
  have hZ₁card : Nat.card Z₁ = 2 := by rw [hZ₁]; exact hZ
  have hZ₂card : Nat.card Z₂ = 2 := by rw [hZ₂]; exact hZ
  have hS₁ne : ∃ x ∈ S₁, x ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hle : S₁ ≤ Z := hcon
    have h1 := Subgroup.card_le_of_le hle
    have h2 := hsp₁.card_eq
    have hn₁ := hsp₁.two_le
    have h3 : 2 ^ 4 ≤ 2 ^ (2 * n₁) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hZ₁card] at h2
    rw [hZ] at h1
    omega
  have hextra : IsExtraspecialPGroup 2 ↥(S₁ ⊔ S₂) := by
    refine PlaneCommuting.isExtraspecialPGroup_sup hS hcomm hZ (hZ₁ ▸ hsp₁.le) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hS₁ne
    · rw [hsp₁.commutator_eq, hZ₁]
    · rw [hsp₂.commutator_eq, hZ₂]
    · intro x hx
      rw [← hZ₁]
      exact hsp₁.sq_mem x hx
    · intro y hy
      rw [← hZ₂]
      exact hsp₂.sq_mem y hy
    · intro z hz y hy
      exact hsp₁.central z (hZ₁ ▸ hz) y hy
    · intro x hx hc
      rw [← hZ₁]
      exact hsp₁.center_le x hx hc
    · intro x hx hc
      rw [← hZ₂]
      exact hsp₂.center_le x hx hc
  have hJ : S₁ ⊓ S₂ = Z := by
    refine le_antisymm (fun j hj => ?_) (le_inf (hZ₁ ▸ hsp₁.le) (hZ₂ ▸ hsp₂.le))
    have := hsp₁.center_le j hj.1 (fun y hy => (hcomm y hy j hj.2).symm)
    rwa [hZ₁] at this
  have hcard := PlaneCommuting.card_sup_mul_card_inf (X := S₁) (Y := S₂) hcomm
  rw [hJ, hZ] at hcard
  have h1 := hsp₁.card_eq
  have h2 := hsp₂.card_eq
  rw [hZ₁card] at h1
  rw [hZ₂card] at h2
  have hS₀card : Nat.card ↥(S₁ ⊔ S₂) = 2 ^ (1 + 2 * (n₁ + n₂)) := by
    rw [h1, h2] at hcard
    have h3 : Nat.card ↥(S₁ ⊔ S₂) * 2 = 2 ^ (1 + 2 * (n₁ + n₂)) * 2 := by
      rw [hcard]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
  have hcenterCard : Nat.card (Subgroup.center ↥(S₁ ⊔ S₂)) = 2 := hextra.2.2.2
  obtain ⟨⟨z, hzc⟩, hz1'⟩ : ∃ z : Subgroup.center ↥(S₁ ⊔ S₂), z ≠ 1 := by
    have : Finite (Subgroup.center ↥(S₁ ⊔ S₂)) :=
      Nat.finite_of_card_ne_zero (by rw [hcenterCard]; norm_num)
    have h : 1 < Nat.card (Subgroup.center ↥(S₁ ⊔ S₂)) := by rw [hcenterCard]; norm_num
    have := Finite.one_lt_card_iff_nontrivial.mp h
    exact exists_ne (1 : Subgroup.center ↥(S₁ ⊔ S₂))
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hcenter : Subgroup.center ↥(S₁ ⊔ S₂) = Subgroup.zpowers z :=
    (zpowers_eq_of_card_two hcenterCard hzc hz1).symm
  have hρinj : Function.Injective ((β.comp SemidirectProduct.inl).comp (S₁ ⊔ S₂).subtype) :=
    (hβ.comp SemidirectProduct.inl_injective).comp (Subgroup.subtype_injective _)
  have hfix : ∀ s : ↥(S₁ ⊔ S₂), s ≠ 1 → CFSG.pRank p (CFSG.RankThree.PartTwo.fixedSubgroupOf
      (((β.comp SemidirectProduct.inl).comp (S₁ ⊔ S₂).subtype) s)) ≤ 3 := by
    intro s hs
    refine PlaneCore.pRank_le_of_forall hp _ fun E hE hEF k hk => ?_
    exact (PlaneSemidirect.le_evenRank_of_fixed β hp hp2 hS (s := (s : S))
      (fun h => hs (Subtype.ext h)) hE (fun e he' => hEF he') hk).trans he
  have hbound := CFSG.RankThree.GroupTheory.SteinbergBM.class_two_extraspecial_action_bound hp2
    hDp hDexp hDcl hextra hS₀card hcenter _ hρinj hfix
  have := hbound.1
  have h4 : 2 ≤ n₁ := hsp₁.two_le
  have h5 : 2 ≤ n₂ := hsp₂.two_le
  omega

end PlaneExtraspecialCase

end CFSG.RankThree.PartOne
