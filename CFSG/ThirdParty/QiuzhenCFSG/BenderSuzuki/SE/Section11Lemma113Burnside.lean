module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113Isaacs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary713

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.3: Burnside endpoint

This module contains the final group-theoretic consequence of the genuine
`[Is1; 3.8, 3.9]` callback.  The callback supplies a proper normal kernel and
centrality modulo that kernel; the contradiction with the ambient two-rank is
proved here, without assuming any conclusion of Lemma 11.3.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- Burnside's prime-power involution-class argument, in the exact
implication-shaped form needed by Lemma 11.3. -/
public theorem lemma113_burnside_prime_power_involution_class_false
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {r n : ℕ}
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hcore : involutionCoreIn M = W)
    (hZne : (involutionsInSet M).Nonempty)
    (hclass : ∀ x : X, x ∈ involutionsInSet M →
      ∀ y : X, y ∈ involutionsInSet M →
        ∃ w : X, w ∈ W ∧ y = rightConjugateElem x w)
    (hr : r.Prime)
    (hZcard : Nat.card (involutionsInSet M) = r ^ n) :
    False := by
  classical
  have hZleW : involutionsInSet M ⊆ W := by
    intro z hz
    rw [← hcore]
    exact involution_mem_involutionCoreIn hz.1 hz.2
  have hZinv : ∀ z : X, z ∈ involutionsInSet M → IsInvolution z := by
    intro z hz
    exact hz.2
  have hWM : W ≤ M := by
    rw [← hcore]
    exact involutionCoreIn_le M
  have hZstable : ∀ z : X, z ∈ involutionsInSet M →
      ∀ w : X, w ∈ W →
        rightConjugateElem z w ∈ involutionsInSet M := by
    intro z hz w hw
    have hwM : w ∈ M := hWM hw
    refine ⟨?_, isInvolution_rightConjugateElem hz.2⟩
    simpa [rightConjugateElem] using
      M.mul_mem (M.mul_mem (M.inv_mem hwM) hz.1) hwM
  obtain ⟨H, hHlt, hHnormal, hcentral⟩ :=
    (is1_38_39 W (involutionsInSet M) r n hr hZne hZleW hZinv
      hZstable hclass hZcard).exists_H
  have hHW : H ≤ W := le_of_lt hHlt
  have hZnotH : ∀ z : X, z ∈ involutionsInSet M → z ∉ H := by
    intro z hzZ hzH
    have hZleH : involutionsInSet M ⊆ H := by
      intro y hyZ
      obtain ⟨w, hwW, hy⟩ := hclass z hzZ y hyZ
      let zW : W := ⟨z, hZleW hzZ⟩
      let wW : W := ⟨w, hwW⟩
      have hzSub : zW ∈ H.subgroupOf W := hzH
      have hconjSub : wW⁻¹ * zW * wW ∈ H.subgroupOf W :=
        hHnormal.conj_mem' zW hzSub wW
      rw [hy]
      simpa [rightConjugateElem, zW, wW, Subgroup.mem_subgroupOf,
        mul_assoc] using hconjSub
    have hWleH : W ≤ H := by
      rw [← hcore, involutionCoreIn, Subgroup.map_le_iff_le_comap,
        involutionCore_eq_closure, Subgroup.closure_le]
      intro y hy
      have hyX : IsInvolution (y : X) :=
        IsInvolution.map_of_injective hy M.subtype M.subtype_injective
      exact hZleH ⟨y.property, hyX⟩
    exact (not_le_of_gt hHlt) hWleH
  obtain ⟨z, hzZ⟩ := hZne
  have hHodd : Odd (Nat.card H) := by
    by_contra hnotOdd
    have hEven : Even (Nat.card H) := Nat.not_odd_iff_even.mp hnotOdd
    have htwo : 2 ∣ Nat.card H := even_iff_two_dvd.mp hEven
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, huOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := H) 2 htwo
    have huData := orderOf_eq_prime_iff.mp huOrder
    have huInvH : IsInvolution u := ⟨huData.2, huData.1⟩
    have huInvX : IsInvolution (u : X) :=
      IsInvolution.map_of_injective huInvH H.subtype H.subtype_injective
    have huW : (u : X) ∈ W := hHW u.property
    have huM : (u : X) ∈ M := hWM huW
    exact hZnotH (u : X) ⟨huM, huInvX⟩ u.property
  have hsup : H ⊔ Subgroup.zpowers z = W := by
    apply le_antisymm
    · exact sup_le hHW (Subgroup.zpowers_le.mpr (hZleW hzZ))
    · rw [← hcore, involutionCoreIn, Subgroup.map_le_iff_le_comap,
        involutionCore_eq_closure, Subgroup.closure_le]
      intro y hy
      have hyX : IsInvolution (y : X) :=
        IsInvolution.map_of_injective hy M.subtype M.subtype_injective
      have hyZ : (y : X) ∈ involutionsInSet M := ⟨y.property, hyX⟩
      obtain ⟨w, hwW, hyConj⟩ := hclass z hzZ (y : X) hyZ
      have hdiff : rightConjugateElem z w * z⁻¹ ∈ H :=
        hcentral z hzZ w hwW
      have hconjMem : rightConjugateElem z w ∈
          H ⊔ Subgroup.zpowers z := by
        have hmul := (H ⊔ Subgroup.zpowers z).mul_mem
          (Subgroup.mem_sup_left hdiff)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
        simpa [mul_assoc] using hmul
      change (y : X) ∈ H ⊔ Subgroup.zpowers z
      rw [hyConj]
      exact hconjMem
  have hWnormH : W ≤ Subgroup.normalizer (H : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHW).mp hHnormal
  have hzNormH : z ∈ Subgroup.normalizer (H : Set X) :=
    hWnormH (hZleW hzZ)
  let fX : involutionCore M →* X :=
    M.subtype.comp (involutionCore M).subtype
  let fW : involutionCore M →* W :=
    fX.codRestrict W (by
      intro y
      rw [← hcore]
      exact Subgroup.mem_map_of_mem M.subtype y.property)
  have hfW : Function.Injective fW := by
    intro a b hab
    have habX : ((a : M) : X) = ((b : M) : X) := by
      simpa [fW, fX] using congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext habX)
  have hrankW : TwoRankAtLeastTwo W :=
    hrank.map_of_injective fW hfW
  have hnotRank :
      ¬ TwoRankAtLeastTwo (H ⊔ Subgroup.zpowers z : Subgroup X) :=
    not_twoRankAtLeastTwo_sup_odd_involution H hHodd hzZ.2 hzNormH
  rw [hsup] at hnotRank
  exact hnotRank hrankW

end CFSG.BenderSuzuki
