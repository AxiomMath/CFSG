module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerRootTransport
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.Universal
  CFSG.LieType.RootSystem
open Matrix TauCeti
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.AUTSL

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

private theorem icalc_mulAut_mul_conj {G : Type*} [Group G] (β : MulAut G) (γ : G) :
    β * MulAut.conj γ = MulAut.conj (β γ) * β := by
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

private theorem icalc_conj_mul_sq {G : Type*} [Group G] (β : MulAut G) (γ : G) :
    (MulAut.conj γ * β) ^ 2 = MulAut.conj (γ * β γ) * β ^ 2 := by
  rw [sq, sq, mul_assoc, ← mul_assoc β, icalc_mulAut_mul_conj, map_mul]
  group

private theorem icalc_conj_mul_pow_two_pow {G : Type*} [Group G] (γ : G) (β : MulAut G)
    (m : ℕ) : ∃ γ' : G, (MulAut.conj γ * β) ^ 2 ^ m = MulAut.conj γ' * β ^ 2 ^ m := by
  induction m with
  | zero => exact ⟨γ, by rw [pow_zero, pow_one, pow_one]⟩
  | succ m ih =>
    obtain ⟨γ', hγ'⟩ := ih
    refine ⟨γ' * (β ^ (2 ^ m)) γ', ?_⟩
    rw [pow_succ, pow_mul, hγ', icalc_conj_mul_sq, pow_mul]

private theorem icalc_theta_mul_refl {K : Type} [Field K] [Finite K] [CharP K 2] :
    (theta : MulAut (Om8 K)) * AutOm.plusRefl (K := K) one_le_four =
      AutOm.plusRefl (K := K) one_le_four * ((theta : MulAut (Om8 K)))⁻¹ := by
  have h := plusRefl_theta_plusRefl (K := K)
  calc (theta : MulAut (Om8 K)) * AutOm.plusRefl one_le_four
      = (AutOm.plusRefl one_le_four * AutOm.plusRefl one_le_four) *
          (theta * AutOm.plusRefl one_le_four) := by
          rw [AutOm.plusRefl_mul_self, one_mul]
    _ = AutOm.plusRefl one_le_four *
          (AutOm.plusRefl one_le_four * theta * AutOm.plusRefl one_le_four) := by group
    _ = AutOm.plusRefl one_le_four * ((theta : MulAut (Om8 K)))⁻¹ := by rw [h]

private theorem icalc_theta_pow_refl {K : Type} [Field K] [Finite K] [CharP K 2] (j : ℕ) :
    (theta : MulAut (Om8 K)) ^ j * AutOm.plusRefl (K := K) one_le_four =
      AutOm.plusRefl (K := K) one_le_four * ((theta : MulAut (Om8 K)) ^ j)⁻¹ := by
  induction j with
  | zero => rw [pow_zero, one_mul, inv_one, mul_one]
  | succ j ih =>
    calc (theta : MulAut (Om8 K)) ^ (j + 1) * AutOm.plusRefl one_le_four
        = ((theta : MulAut (Om8 K)) ^ j * theta) * AutOm.plusRefl one_le_four := by
            rw [pow_succ]
      _ = (theta : MulAut (Om8 K)) ^ j *
            (theta * AutOm.plusRefl one_le_four) := by group
      _ = (theta : MulAut (Om8 K)) ^ j *
            (AutOm.plusRefl one_le_four * ((theta : MulAut (Om8 K)))⁻¹) := by
            rw [icalc_theta_mul_refl]
      _ = ((theta : MulAut (Om8 K)) ^ j * AutOm.plusRefl one_le_four) *
            ((theta : MulAut (Om8 K)))⁻¹ := by group
      _ = (AutOm.plusRefl one_le_four * ((theta : MulAut (Om8 K)) ^ j)⁻¹) *
            ((theta : MulAut (Om8 K)))⁻¹ := by rw [ih]
      _ = AutOm.plusRefl one_le_four *
            (((theta : MulAut (Om8 K)) ^ j)⁻¹ * ((theta : MulAut (Om8 K)))⁻¹) := by group
      _ = AutOm.plusRefl one_le_four * ((theta : MulAut (Om8 K)) ^ (j + 1))⁻¹ := by
            rw [← _root_.mul_inv_rev, ← pow_succ']

private theorem icalc_theta_pow_mul_refl_field {K : Type} [Field K] [Finite K] [CharP K 2]
    (k : ℕ) (σ : K ≃+* K) :
    (theta : MulAut (Om8 K)) ^ k *
        ((theta : MulAut (Om8 K)) ^ k *
          (AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 σ)) *
      ((theta : MulAut (Om8 K)) ^ k)⁻¹ =
    AutOm.plusRefl (K := K) one_le_four * AutOm.fieldAutP 4 σ := by
  have hρ : (theta : MulAut (Om8 K)) ^ k * AutOm.plusRefl (K := K) one_le_four =
      AutOm.plusRefl (K := K) one_le_four * ((theta : MulAut (Om8 K)) ^ k)⁻¹ :=
    icalc_theta_pow_refl k
  have hfT : Commute (AutOm.fieldAutP 4 σ) ((theta : MulAut (Om8 K)) ^ k) :=
    Commute.pow_right (theta_fieldAutP σ).symm k
  have hfTinv : AutOm.fieldAutP 4 σ * ((theta : MulAut (Om8 K)) ^ k)⁻¹ =
      ((theta : MulAut (Om8 K)) ^ k)⁻¹ * AutOm.fieldAutP 4 σ := hfT.inv_right.eq
  have h3 : ((theta : MulAut (Om8 K)) ^ k)⁻¹ * ((theta : MulAut (Om8 K)) ^ k)⁻¹ *
      ((theta : MulAut (Om8 K)) ^ k)⁻¹ = 1 := by
    have h3' : ((theta : MulAut (Om8 K)) ^ k)⁻¹ * ((theta : MulAut (Om8 K)) ^ k)⁻¹ *
        ((theta : MulAut (Om8 K)) ^ k)⁻¹ =
        (((theta : MulAut (Om8 K)) ^ k)⁻¹) ^ 3 := by group
    rw [h3', inv_pow, ← pow_mul, mul_comm k 3, pow_mul, theta_cube, one_pow, inv_one]
  calc (theta : MulAut (Om8 K)) ^ k *
        ((theta : MulAut (Om8 K)) ^ k *
          (AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 σ)) *
        ((theta : MulAut (Om8 K)) ^ k)⁻¹
      = (theta : MulAut (Om8 K)) ^ k *
          (((theta : MulAut (Om8 K)) ^ k * AutOm.plusRefl one_le_four) *
            AutOm.fieldAutP 4 σ) * ((theta : MulAut (Om8 K)) ^ k)⁻¹ := by group
    _ = (theta : MulAut (Om8 K)) ^ k *
          ((AutOm.plusRefl one_le_four * ((theta : MulAut (Om8 K)) ^ k)⁻¹) *
            AutOm.fieldAutP 4 σ) * ((theta : MulAut (Om8 K)) ^ k)⁻¹ := by rw [hρ]
    _ = (theta : MulAut (Om8 K)) ^ k * AutOm.plusRefl one_le_four *
          ((theta : MulAut (Om8 K)) ^ k)⁻¹ * AutOm.fieldAutP 4 σ *
          ((theta : MulAut (Om8 K)) ^ k)⁻¹ := by group
    _ = (AutOm.plusRefl one_le_four * ((theta : MulAut (Om8 K)) ^ k)⁻¹) *
          ((theta : MulAut (Om8 K)) ^ k)⁻¹ * AutOm.fieldAutP 4 σ *
          ((theta : MulAut (Om8 K)) ^ k)⁻¹ := by rw [hρ]
    _ = AutOm.plusRefl one_le_four * ((theta : MulAut (Om8 K)) ^ k)⁻¹ *
          ((theta : MulAut (Om8 K)) ^ k)⁻¹ *
          (AutOm.fieldAutP 4 σ * ((theta : MulAut (Om8 K)) ^ k)⁻¹) := by group
    _ = AutOm.plusRefl one_le_four * ((theta : MulAut (Om8 K)) ^ k)⁻¹ *
          ((theta : MulAut (Om8 K)) ^ k)⁻¹ *
          (((theta : MulAut (Om8 K)) ^ k)⁻¹ * AutOm.fieldAutP 4 σ) := by rw [hfTinv]
    _ = AutOm.plusRefl one_le_four * (((theta : MulAut (Om8 K)) ^ k)⁻¹ *
          ((theta : MulAut (Om8 K)) ^ k)⁻¹ * ((theta : MulAut (Om8 K)) ^ k)⁻¹) *
          AutOm.fieldAutP 4 σ := by group
    _ = AutOm.plusRefl one_le_four * 1 * AutOm.fieldAutP 4 σ := by rw [h3]
    _ = AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 σ := by group

private theorem icalc_theta_pow_eq_one_of_pow_two_pow_mul_eq_one {K : Type} [Field K]
    [Finite K] [CharP K 2] {k m : ℕ}
    (h : (theta : MulAut (Om8 K)) ^ (k * 2 ^ m) = 1) :
    (theta : MulAut (Om8 K)) ^ k = 1 := by
  have hdvd3 : orderOf (theta : MulAut (Om8 K)) ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr theta_cube
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd3 with h1 | h3
  · rw [orderOf_eq_one_iff.mp h1, one_pow]
  · have hdvdN : orderOf (theta : MulAut (Om8 K)) ∣ k * 2 ^ m :=
      orderOf_dvd_iff_pow_eq_one.mpr h
    rw [h3] at hdvdN
    obtain ⟨t, ht⟩ :=
      (Nat.Coprime.pow_right m (by decide : Nat.Coprime 3 2)).dvd_of_dvd_mul_right hdvdN
    rw [ht, pow_mul, theta_cube, one_pow]

theorem exists_conjAct_of_mem_inner_mul_plusCompl {K : Type} [Field K] [Finite K] [CharP K 2]
    {α : MulAut (Om8 K)}
    (h : ∃ ι ∈ inner (Om8 K), ∃ c ∈ AutOm.plusCompl (K := K) one_le_four, α = ι * c) :
    ∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = α := by
  obtain ⟨ι, hι, c, hc, rfl⟩ := h
  obtain ⟨gι, hgι⟩ := exists_pair_of_mem_inner hι
  obtain ⟨gc, hgc⟩ := exists_pair_of_mem_plusCompl hc
  exact ⟨gι * gc, by rw [map_mul, hgι, hgc]⟩

theorem exists_theta_pow_conj_mem_inner_mul_plusCompl {K : Type} [Field K] [Finite K] [CharP K 2]
    (α : MulAut (Om8 K)) (m : ℕ) (hα : α ^ 2 ^ m = 1) :
    ∃ j : ℕ, ∃ ι ∈ inner (Om8 K), ∃ c ∈ AutOm.plusCompl (K := K) one_le_four,
      (theta : MulAut (Om8 K)) ^ j * α * ((theta : MulAut (Om8 K)) ^ j)⁻¹ = ι * c := by
  obtain ⟨ι, hι, k, c, hc, hαe⟩ := exists_inner_mul_theta_pow_mul α
  obtain ⟨γ, rfl⟩ := hι
  obtain ⟨σ, rfl | rfl⟩ := hc
  ·
    have hθk : (theta : MulAut (Om8 K)) ^ k = 1 := by
      have hxmem : ((theta : MulAut (Om8 K)) ^ k * AutOm.fieldAutP 4 σ) ^ 2 ^ m ∈
          inner (Om8 K) := by
        obtain ⟨γ', hγ'⟩ := icalc_conj_mul_pow_two_pow γ
          ((theta : MulAut (Om8 K)) ^ k * AutOm.fieldAutP 4 σ) m
        rw [hαe, hγ'] at hα
        refine ⟨γ'⁻¹, ?_⟩
        rw [map_inv, eq_inv_of_mul_eq_one_right hα]
      have hpow : ((theta : MulAut (Om8 K)) ^ k * AutOm.fieldAutP 4 σ) ^ 2 ^ m =
          (theta : MulAut (Om8 K)) ^ (k * 2 ^ m) * AutOm.fieldAutP 4 (σ ^ 2 ^ m) := by
        rw [Commute.mul_pow (Commute.pow_left (theta_fieldAutP σ) k) (2 ^ m), ← pow_mul,
          ← map_pow]
      have hmem' : (theta : MulAut (Om8 K)) ^ (k * 2 ^ m) *
          AutOm.fieldAutP 4 (σ ^ 2 ^ m) ∈ inner (Om8 K) := by
        rwa [← hpow]
      exact icalc_theta_pow_eq_one_of_pow_two_pow_mul_eq_one
        (theta_pow_mul_mem_inner (k * 2 ^ m) ⟨σ ^ 2 ^ m, Or.inl rfl⟩ hmem').1
    refine ⟨0, MulAut.conj γ, ⟨γ, rfl⟩, AutOm.fieldAutP 4 σ, ⟨σ, Or.inl rfl⟩, ?_⟩
    rw [pow_zero, one_mul, inv_one, mul_one, hαe, hθk, one_mul]
  ·
    refine ⟨k, (theta : MulAut (Om8 K)) ^ k * MulAut.conj γ *
        ((theta : MulAut (Om8 K)) ^ k)⁻¹,
      (inner_normal (Om8 K)).conj_mem (MulAut.conj γ) ⟨γ, rfl⟩ ((theta : MulAut (Om8 K)) ^ k),
      AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 σ, ⟨σ, Or.inr rfl⟩, ?_⟩
    rw [hαe]
    calc (theta : MulAut (Om8 K)) ^ k *
          (MulAut.conj γ * ((theta : MulAut (Om8 K)) ^ k *
            (AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 σ))) *
          ((theta : MulAut (Om8 K)) ^ k)⁻¹
        = ((theta : MulAut (Om8 K)) ^ k * MulAut.conj γ *
            ((theta : MulAut (Om8 K)) ^ k)⁻¹) *
          ((theta : MulAut (Om8 K)) ^ k *
            ((theta : MulAut (Om8 K)) ^ k *
              (AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 σ)) *
            ((theta : MulAut (Om8 K)) ^ k)⁻¹) := by group
      _ = ((theta : MulAut (Om8 K)) ^ k * MulAut.conj γ *
            ((theta : MulAut (Om8 K)) ^ k)⁻¹) *
          (AutOm.plusRefl one_le_four * AutOm.fieldAutP 4 σ) := by
            rw [icalc_theta_pow_mul_refl_field k σ]

theorem exists_theta_pow_conj_eq_conjAct {K : Type} [Field K] [Finite K] [CharP K 2]
    (α : MulAut (Om8 K)) (m : ℕ) (hα : α ^ 2 ^ m = 1) :
    ∃ j : ℕ, ∃ g : similarityPairs (coordinateQuadPlus 4 K),
      (theta : MulAut (Om8 K)) ^ j * α * ((theta : MulAut (Om8 K)) ^ j)⁻¹ = conjAct _ g := by
  obtain ⟨j, ι, hι, c, hc, h⟩ := exists_theta_pow_conj_mem_inner_mul_plusCompl α m hα
  obtain ⟨g, hg⟩ := exists_conjAct_of_mem_inner_mul_plusCompl ⟨ι, hι, c, hc, h⟩
  exact ⟨j, g, hg.symm⟩

end CFSG.StandardType.LieKnownR2.POmega.Inner
