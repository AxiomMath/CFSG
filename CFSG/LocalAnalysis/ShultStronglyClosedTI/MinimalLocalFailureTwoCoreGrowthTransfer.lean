module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthTransferPower
public import CFSG.LocalAnalysis.LargeEvenClassification.RankOneComparable

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

theorem cyclic_two_group_has_normal_index_two
    (A : Type u) [Group A] [Finite A] [IsCyclic A] [Nontrivial A]
    (hA : IsPGroup 2 A) :
    ∃ D : Subgroup A, D.Normal ∧ D.index = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CommGroup A := IsCyclic.commGroup
  let D : Subgroup A := (powMonoidHom 2 : A →* A).range
  have hdiv : 2 ∣ Nat.card A := hA.card_eq_or_dvd.resolve_left (by
    have hcard := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial A)
    omega)
  refine ⟨D, inferInstance, ?_⟩
  change (powMonoidHom 2 : A →* A).range.index = 2
  rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right_iff_dvd.mpr hdiv]

theorem thompson_cyclic_two_quotient_transfer
    (S : Sylow 2 G) (N : Subgroup (S : Subgroup G)) [N.Normal]
    [IsCyclic ((S : Subgroup G) ⧸ N)]
    (x : (S : Subgroup G)) (hx : x ∉ N) (hxorder : orderOf x = 2)
    (havoid : ∀ (g : G) (hmem : g⁻¹ * (x : G) * g ∈ (S : Subgroup G)),
      (⟨g⁻¹ * (x : G) * g, hmem⟩ : (S : Subgroup G)) ∉ N) :
    let T := (QuotientGroup.mk' N).transfer
    T.ker.Normal ∧
      (x : G) ∉ T.ker ∧
      Nontrivial (G ⧸ T.ker) ∧
      Finite (G ⧸ T.ker) ∧
      IsCyclic (G ⧸ T.ker) ∧
      IsPGroup 2 (G ⧸ T.ker) ∧
      ∃ D : Subgroup G, D.Normal ∧ D.index = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := (S : Subgroup G) ⧸ N
  let f : (S : Subgroup G) →* Q := QuotientGroup.mk' N
  have hxinvol : orderOf (f x) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [hxorder, map_pow, map_one] using congrArg f (pow_orderOf_eq_one x)
    · exact fun hzero => hx ((QuotientGroup.eq_one_iff x).mp hzero)
  have hconj (g : G) (hmem : g⁻¹ * (x : G) * g ∈ (S : Subgroup G)) :
      f ⟨g⁻¹ * (x : G) * g, hmem⟩ = f x := by
    let y : (S : Subgroup G) := ⟨g⁻¹ * (x : G) * g, hmem⟩
    have hyorder : orderOf y = 2 := by
      have hh := (MulAut.conj g⁻¹).orderOf_eq (x : G)
      simp only [MulAut.conj_apply, inv_inv] at hh
      exact (Subgroup.orderOf_coe y).symm.trans
        (hh.trans ((Subgroup.orderOf_coe x).trans hxorder))
    have hyinvol : orderOf (f y) = 2 := by
      apply orderOf_eq_prime_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa only [hyorder, map_pow, map_one] using congrArg f (pow_orderOf_eq_one y)
      · exact fun hzero => havoid g hmem ((QuotientGroup.eq_one_iff y).mp hzero)
    exact CFSG.LargeEvenClassification.Helpers.cyclic_two_group_involutions_unique
      (f y) (f x) hyinvol hxinvol
  have hfusion : ∀ (k : ℕ) (g : G)
      (hmem : g⁻¹ * (x : G) ^ k * g ∈ (S : Subgroup G)),
      f ⟨g⁻¹ * (x : G) ^ k * g, hmem⟩ = f (x ^ k) := by
    intro k g hmem
    have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    have hxpow : x ^ k = x ^ (k % 2) := by
      simpa only [hxorder] using (pow_mod_orderOf x k).symm
    rcases hmod with hzero | hone
    · have hpow : x ^ k = 1 := by rw [hxpow, hzero, pow_zero]
      have hpowG : (x : G) ^ k = 1 := congrArg Subtype.val hpow
      have hyone : (⟨g⁻¹ * (x : G) ^ k * g, hmem⟩ : (S : Subgroup G)) = 1 := by
        apply Subtype.ext
        simp only [hpowG, mul_one, inv_mul_cancel, Subgroup.coe_one]
      rw [hyone, hpow]
    · have hpow : x ^ k = x := by rw [hxpow, hone, pow_one]
      have hpowG : (x : G) ^ k = x := congrArg Subtype.val hpow
      have hy : (⟨g⁻¹ * (x : G) ^ k * g, hmem⟩ : (S : Subgroup G)) =
          ⟨g⁻¹ * (x : G) * g, hpowG ▸ hmem⟩ :=
        Subtype.ext (congrArg (fun a : G => g⁻¹ * a * g) hpowG)
      rw [hy, hpow]
      exact hconj g _
  have hdetection := power_fusion_transfer_detection 2 Nat.prime_two S N x hx hfusion
  let T : G →* Q := f.transfer
  have hxnker : (x : G) ∉ T.ker := hdetection.2.2.2.1
  have hnontrivial : Nontrivial (G ⧸ T.ker) := hdetection.2.2.2.2.1
  have htwo : IsPGroup 2 (G ⧸ T.ker) := hdetection.2.2.2.2.2.2.2
  let e : G ⧸ T.ker ≃* T.range := QuotientGroup.quotientKerEquivRange T
  have hcyclic : IsCyclic (G ⧸ T.ker) := isCyclic_of_injective
    (T.range.subtype.comp e.toMonoidHom) (Subtype.val_injective.comp e.injective)
  have hindex : ∃ D : Subgroup G, D.Normal ∧ D.index = 2 := by
    let : Nontrivial (G ⧸ T.ker) := hnontrivial
    let : IsCyclic (G ⧸ T.ker) := hcyclic
    obtain ⟨D, hDnormal, hDindex⟩ :=
      cyclic_two_group_has_normal_index_two (G ⧸ T.ker) htwo
    let : D.Normal := hDnormal
    let q : G →* G ⧸ T.ker := QuotientGroup.mk' T.ker
    refine ⟨D.comap q, inferInstance, ?_⟩
    rw [Subgroup.index_comap_of_surjective D (QuotientGroup.mk'_surjective T.ker)]
    exact hDindex
  exact ⟨inferInstance, hxnker, hnontrivial, inferInstance, hcyclic, htwo, hindex⟩

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
