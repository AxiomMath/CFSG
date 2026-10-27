module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25Fitting
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17iii

namespace CFSG
end CFSG
open CFSG

/-!
# Assembly of the non-`p` branch of Gorenstein--Walter Lemma 2.5

Once the component layer of the controlled conjugate is also contained in
the original maximal subgroup, the proved Fitting containment gives the
full reverse `F*` containment and Bender 1.7(iii) forces equality.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem lemma25_two_le_card_primesOfOrder_of_not_isPGroup
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (hnp : ∀ p : ℕ, p.Prime → ¬ IsPGroup p H) :
    2 ≤ Nat.card (primesOfOrder H) := by
  by_contra hnot
  have hle : Nat.card (primesOfOrder H) ≤ 1 := by omega
  have hset : primesOfOrder H = ↑((Nat.card (↥H)).primeFactors) := by
    ext r
    simp [primesOfOrder]
  have hpfle : (Nat.card (↥H)).primeFactors.card ≤ 1 := by
    change (primesOfOrder H).ncard ≤ 1 at hle
    rw [hset] at hle
    simpa using hle
  by_cases hcard1 : Nat.card (↥H) = 1
  · have hP : IsPGroup 2 H := by
      refine IsPGroup.of_card (n := 0) ?_
      simpa [hcard1]
    exact hnp 2 Nat.prime_two hP
  · have hpfne : (Nat.card (↥H)).primeFactors.card ≠ 0 := by
      intro hzero
      have hempty : (Nat.card (↥H)).primeFactors = ∅ :=
        Finset.card_eq_zero.mp hzero
      have hzero_or_one : Nat.card (↥H) = 0 ∨ Nat.card (↥H) = 1 :=
        Nat.primeFactors_eq_empty.mp hempty
      exact hzero_or_one.elim (fun hzero => Nat.card_pos.ne' hzero) hcard1
    have hpfeq : (Nat.card (↥H)).primeFactors.card = 1 := by omega
    have hpow : IsPrimePow (Nat.card (↥H)) :=
      isPrimePow_iff_card_primeFactors_eq_one.mpr hpfeq
    rcases (isPrimePow_nat_iff (Nat.card (↥H))).mp hpow with
      ⟨p, n, hp, _hn, hcard⟩
    have hP : IsPGroup p H := IsPGroup.of_card (n := n) hcard.symm
    exact hnp p hp hP

/-- The non-`p` branch of Lemma 2.5, conditional only on the remaining
component-layer containment. -/
public theorem eq_conjugateSubgroup_of_controlCore_of_not_isPGroup_of_componentLayer_le
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A) (g : G)
    (hC : ControlCore A (conjugateSubgroup A g))
    (hnp : ∀ p : ℕ, p.Prime →
      ¬ IsPGroup p (generalizedFittingSubgroupOf A))
    (hEB : componentLayerOf (conjugateSubgroup A g) ≤ A) :
    A = conjugateSubgroup A g := by
  let B : Subgroup G := conjugateSubgroup A g
  have hB : IsCoatom B := by
    dsimp [B, conjugateSubgroup]
    exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup A).2 hA
  rcases hC with ⟨S, hSne, hSF, hSB, hSsub, hCS⟩
  have hFB : fittingSubgroupOf B ≤ A :=
    fittingSubgroupOf_conjugateSubgroup_le_of_controlCore_of_not_isPGroup
      hsimple A hA g ⟨S, hSne, hSF, hSB, hSsub, hCS⟩ hnp
  have hFstarB : generalizedFittingSubgroupOf B ≤ A := by
    rw [generalizedFittingSubgroupOf]
    exact sup_le hFB hEB
  have hpi : 2 ≤ Nat.card
      (primesOfOrder (generalizedFittingSubgroupOf A)) :=
    lemma25_two_le_card_primesOfOrder_of_not_isPGroup
      (generalizedFittingSubgroupOf A) hnp
  apply bender1970_1_7_iii_equalityOfMaximal hsimple A hA S hSF hSsub hCS
    hSB hB (Or.inl hpi)
  refine ⟨generalizedFittingSubgroupOf B, hFstarB, le_rfl, ?_, ?_⟩
  · have heq : (generalizedFittingSubgroupOf B).subgroupOf
        (generalizedFittingSubgroupOf B) = ⊤ := by
      ext x
      simp
    rw [heq]
    exact Subgroup.IsSubnormal.top
  · exact inf_le_left

end CFSG.GorensteinWalter
