module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofE9
public import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix
import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def KF82D4OuterClasses : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
    ∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      α ^ 3 = 1 → ¬ KFacts.IsInnerAut α →
        Sec4.IsStdGraphFieldConj σ α ∨
          ∃ (γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
            (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
            Sec4.IsStdGraphFieldConj σ γ ∧ γ y = y ∧ orderOf y = 3 ∧ α = γ * MulAut.conj y

namespace Item8KFactsProof

theorem ringChar_eq_two_of_card {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) : ringChar K = 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 3) (by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  exact ringChar.eq K 2

theorem exists_pair_autFix_of_isStdGraphFieldConj {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (σ : K ≃+* K)
    {γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hγ : Sec4.IsStdGraphFieldConj σ γ) :
    ∃ u v : Sec4.autFix γ, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u := by
  obtain ⟨φ⟩ := KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2 σ hK2
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀
  have hfix : Sec4.autFix σ₀ = σ₀.toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext x
    rfl
  have hfixinv : Sec4.autFix σ₀⁻¹ = Sec4.autFix σ₀ := by
    ext x
    rw [Sec4.mem_autFix, Sec4.mem_autFix]
    constructor
    · intro h
      have := congrArg σ₀ h
      rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
      exact this.symm
    · intro h
      rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
      exact h.symm
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := Sec11.KS11Lie2Proof.g2_exists_e9 (fixSubfield σ)
  have hpair₀ : ∃ u v : Sec4.autFix σ₀, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u :=
    exists_pair_of_injective
      ((MulEquiv.subgroupCongr hfix).trans φ).symm.toMonoidHom
      ((MulEquiv.subgroupCongr hfix).trans φ).symm.injective ⟨u, v, hu1, hu3, hv3, huv, hvu⟩
  have hcongr : ∀ (β ρ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      β * ρ * β⁻¹ = MulAut.congr β ρ := by
    intro β ρ
    ext x
    rfl
  obtain ⟨β, hβ | hβ⟩ := hγ
  · rw [hβ, hcongr]
    exact exists_pair_of_injective (Sec4.autFixCongrEquiv β σ₀).symm.toMonoidHom
      (Sec4.autFixCongrEquiv β σ₀).symm.injective hpair₀
  · rw [hβ, hcongr]
    have hpair₁ : ∃ u v : Sec4.autFix σ₀⁻¹, u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
        v ∉ Subgroup.zpowers u :=
      exists_pair_of_injective (MulEquiv.subgroupCongr hfixinv).symm.toMonoidHom
        (MulEquiv.subgroupCongr hfixinv).symm.injective hpair₀
    exact exists_pair_of_injective (Sec4.autFixCongrEquiv β σ₀⁻¹).symm.toMonoidHom
      (Sec4.autFixCongrEquiv β σ₀⁻¹).symm.injective hpair₁

theorem e9Closed_autFix_of_isStdGraphFieldConj {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (σ : K ≃+* K)
    {γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hγ : Sec4.IsStdGraphFieldConj σ γ) : E9Closed (Sec4.autFix γ) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := exists_pair_autFix_of_isStdGraphFieldConj hK2 σ hγ
  exact e9Closed_of_commuting hu1 hu3 hv3 huv hvu

theorem exists_pair_autFix_mul_conj {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (σ : K ≃+* K)
    {γ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hγ : Sec4.IsStdGraphFieldConj σ γ) (hγy : γ y = y) (hy : orderOf y = 3) :
    ∃ u v : Sec4.autFix (γ * MulAut.conj y), u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u := by
  have hE9 := e9Closed_autFix_of_isStdGraphFieldConj hK2 σ hγ
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    omega
  set y' : Sec4.autFix γ := ⟨y, hγy⟩ with hy'
  obtain ⟨z, hz3, hyz, hzy⟩ := hE9 y' (Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3))
    (fun h => hy1 (congrArg Subtype.val h))
  have hyα : (γ * MulAut.conj y) y = y := by
    rw [MulAut.mul_apply, MulAut.conj_apply, mul_inv_cancel_right, hγy]
  have hzc : (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) * y = y * z := by
    have := congrArg Subtype.val hyz
    exact this.symm
  have hzα : (γ * MulAut.conj y) z = z := by
    rw [MulAut.mul_apply, MulAut.conj_apply, ← hzc, mul_inv_cancel_right]
    exact z.2
  have hz3' : (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ^ 3 = 1 := by
    have := congrArg Subtype.val hz3
    rwa [Subgroup.coe_pow] at this
  refine ⟨⟨y, hyα⟩, ⟨z, hzα⟩, fun h => hy1 (congrArg Subtype.val h),
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hy3),
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hz3'),
    Subtype.ext hzc.symm, fun h => hzy ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  have := congrArg Subtype.val hk
  rw [Subgroup.coe_zpow] at this ⊢
  exact this

end Item8KFactsProof

open Item8KFactsProof

theorem kF82E9TrialityD4_of (hC : KF82D4OuterClasses) : KF82E9TrialityD4 := by
  intro X _ n hX α hα3 hαin
  obtain ⟨K, _, _, σ, hK, hσ, ⟨E⟩⟩ := Sec4.exists_mulEquiv_graphFixedRootGroup_D4 hX
  have hK2 := ringChar_eq_two_of_card hK
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite X := Finite.of_equiv _ E.symm.toEquiv
  set α' := MulAut.congr E α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, hα3, map_one]
  have hα'in : ¬ KFacts.IsInnerAut α' := fun h => hαin ((KFacts.isInnerAut_congr E α).mp h)
  have hpair : ∃ u v : Sec4.autFix α', u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u := by
    rcases hC n K σ hK hσ α' hα'3 hα'in with hstd | ⟨γ, y, hγ, hγy, hy, hαγ⟩
    · exact exists_pair_autFix_of_isStdGraphFieldConj hK2 σ hstd
    · rw [hαγ]
      exact exists_pair_autFix_mul_conj hK2 σ hγ hγy hy
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := exists_pair_of_injective
    (Sec4.autFixCongrEquiv E α).toMonoidHom (Sec4.autFixCongrEquiv E α).injective hpair
  exact e9Closed_of_commuting hu1 hu3 hv3 huv hvu

end CFSG.RankThree.PartTwo.Sec8
