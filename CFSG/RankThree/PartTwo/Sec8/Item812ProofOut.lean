module

public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open CFSG.Assembly.RankThreeEven (projSp)

theorem isInnerAut_commutator_statedSp_two {K : Type} [Field K] [Finite K] {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (σ τ : MulAut (StatedProj (StatedSp 2 K))) :
    IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hm hK
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hm hK
  obtain ⟨-, -, -, -, hcyc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure hm hFr hord
      hzp
  set π := QuotientGroup.mk' (inner (StatedProj (StatedSp 2 K))) with hπ
  have hc : π σ * π τ = π τ * π σ := hcyc.commGroup.mul_comm _ _
  have h : π (σ * τ * σ⁻¹ * τ⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

theorem isInnerAut_commutator_of_mulEquiv_projSp_two {X : Type*} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (e : X ≃* projSp 2 (GaloisField 2 m)) (σ τ : MulAut X) :
    IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  set e' := e.trans (projSpEquivStatedProj 2 (GaloisField 2 m))
  have h := isInnerAut_commutator_statedSp_two hm (GaloisField.card 2 m (by omega))
    (MulAut.congr e' σ) (MulAut.congr e' τ)
  rwa [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, isInnerAut_congr] at h

theorem isInnerAut_of_conj_eq_inv {M : Type*} [Group M]
    (hOut : ∀ σ τ : MulAut M, IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹)) {α κ : MulAut M}
    (h3 : α ^ 3 = 1) (hκ : κ⁻¹ * α * κ = α⁻¹) : IsInnerAut α := by
  have h := hOut α⁻¹ κ⁻¹
  have e : α⁻¹ * κ⁻¹ * α⁻¹⁻¹ * κ⁻¹⁻¹ = α := by
    calc α⁻¹ * κ⁻¹ * α⁻¹⁻¹ * κ⁻¹⁻¹ = α⁻¹ * (κ⁻¹ * α * κ) := by group
      _ = α⁻¹ * α⁻¹ * α ^ 3 := by rw [hκ, h3, mul_one]
      _ = α := by group
  rwa [e] at h

variable {G : Type*} [Group G] [Finite G]

theorem not_inducesOuterTheta_of_conj_eq_inv {X : Subgroup G}
    (hOut : ∀ σ τ : MulAut (X ⧸ aschbacherSolvableCore 3 X), IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹))
    {a k : G} (hk : k ∈ Subgroup.normalizer (X : Set G)) (ha3 : a ^ 3 = 1)
    (hka : k⁻¹ * a * k = a⁻¹) : ¬ InducesOuterTheta a X := by
  rintro ⟨ha, hout⟩
  set φ := (thetaQuotMulAut X).comp (compAction X) with hφ
  have hα3 : φ ⟨a, ha⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, ha⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this, map_one]
  have hκ : (φ ⟨k, hk⟩)⁻¹ * φ ⟨a, ha⟩ * φ ⟨k, hk⟩ = (φ ⟨a, ha⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using hka)
  exact hout (isInnerAut_of_conj_eq_inv hOut hα3 hκ)

theorem not_inducesOuterTheta_of_conj_eq_inv_of_projSp {X : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 m))) {a k : G}
    (hk : k ∈ Subgroup.normalizer (X : Set G)) (ha3 : a ^ 3 = 1) (hka : k⁻¹ * a * k = a⁻¹) :
    ¬ InducesOuterTheta a X :=
  not_inducesOuterTheta_of_conj_eq_inv
    (isInnerAut_commutator_of_mulEquiv_projSp_two hm hX.some) hk ha3 hka

end CFSG.RankThree.PartTwo.Sec8
