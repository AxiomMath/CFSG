module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

open CFSG

theorem exists_perfect_cover {M : Type*} [Group M] [Finite M] (R : Subgroup M) [R.Normal]
    (J : Subgroup (M ⧸ R)) [hJ : Group.IsPerfect J] :
    ∃ X : Subgroup M, Group.IsPerfect X ∧ X.map (QuotientGroup.mk' R) = J := by
  classical
  set q := QuotientGroup.mk' R with hq
  have hex : ∃ n : ℕ, ∃ X : Subgroup M, X.map q = J ∧ Nat.card X = n :=
    ⟨_, J.comap q, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) J,
      rfl⟩
  obtain ⟨X, hXJ, hXn⟩ := Nat.find_spec hex
  refine ⟨X, ?_, hXJ⟩
  have hX'J : (⁅X, X⁆).map q = J := by
    rw [Subgroup.map_commutator, hXJ]
    exact Subgroup.commutator_eq_self
  have hle : Nat.find hex ≤ Nat.card (⁅X, X⁆ : Subgroup M) :=
    Nat.find_min' hex ⟨⁅X, X⁆, hX'J, rfl⟩
  have hX'le : (⁅X, X⁆ : Subgroup M) ≤ X := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem h₁ h₂) (X.inv_mem h₁)) (X.inv_mem h₂)
  have heq : (⁅X, X⁆ : Subgroup M) = X :=
    Subgroup.eq_of_le_of_card_ge hX'le (by rw [hXn]; exact hle)
  exact Subgroup.isPerfect_iff.mpr heq

theorem normal_map_pPrimeCore {M : Type*} [Group M] [Finite M] (R : Subgroup M) [R.Normal]
    (p : ℕ) : ((CFSG.pPrimeCore p R).map R.subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨r, hr, rfl⟩ g
  refine ⟨MulAut.conjNormal g r, ?_, ?_⟩
  · have hchar : (CFSG.pPrimeCore p R).Characteristic := inferInstance
    exact (Subgroup.characteristic_iff_le_comap.mp hchar (MulAut.conjNormal g)) hr
  · simp [MulAut.conjNormal_apply]

theorem odd_card_of_hom {G H : Type*} [Group G] [Finite G] [Group H] (f : G →* H)
    (hker : Odd (Nat.card f.ker)) (hrange : Odd (Nat.card f.range)) : Odd (Nat.card G) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have e : G ⧸ f.ker ≃* f.range := QuotientGroup.quotientKerEquivRange f
  rw [h, Nat.card_congr e.toEquiv]
  exact hrange.mul hker

end CFSG.RankThree.PartTwo.Sec13.K135SF
