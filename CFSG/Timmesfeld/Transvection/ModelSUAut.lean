module


import CFSG.LocalAnalysis.StandardType.GGRootDetectSU
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
import CFSG.Timmesfeld.LieEmbed.UnitaryIsometry
import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinearSU
import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeRadical
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUTorus
public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.Timmesfeld.LieEmbed.UnitaryWitt

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem uForm_mulVec_of_isometry {M : Matrix (Fin n) (Fin n) F}
    (hM : conjTr σ M * antidiag n * M = antidiag n) (x y : Fin n → F) :
    uForm σ (M *ᵥ x) (M *ᵥ y) = uForm σ x y :=
  (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_isometry_iff σ M).2 hM x y

private theorem map_antidiag (φ : F ≃+* F) (n : ℕ) :
    (antidiag n : Matrix (Fin n) (Fin n) F).map φ = antidiag n := by
  ext i j
  simp only [Matrix.map_apply, antidiag, Matrix.of_apply]
  split_ifs <;> simp

private theorem map_conjTr (φ : F ≃+* F) (hφ : ∀ c, φ (σ c) = σ (φ c))
    (M : Matrix (Fin n) (Fin n) F) :
    (conjTr σ M).map φ = conjTr σ (M.map φ) := by
  ext i j
  simp only [conjTr, Matrix.map_apply, Matrix.transpose_apply]
  exact hφ (M j i)

private theorem conjTr_scalar (u : F) :
    conjTr σ (Matrix.scalar (Fin n) u) = Matrix.scalar (Fin n) (σ u) := by
  rw [conjTr, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ),
    Matrix.diagonal_transpose]

private theorem conjTr_scalar_mul_antidiag_mul_scalar (u : F) :
    conjTr σ (Matrix.scalar (Fin n) u) * antidiag n * Matrix.scalar (Fin n) u =
      (σ u * u) • antidiag n := by
  rw [conjTr_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Matrix.smul_mul, ← Matrix.smul_eq_mul_diagonal, smul_smul]

structure IsSemilinearLift {K : Type*} [Group K] (Φ : SU σ n →* K) (y : K)
    (A : GL (Fin n) F) (φ : F ≃+* F) (α : SU σ n →* SU σ n) : Prop where
  isometry : conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
    (A : Matrix (Fin n) (Fin n) F) = antidiag n
  comm : ∀ c, φ (σ c) = σ (φ c)
  mat : ∀ g, suMat σ n (α g) * (A : Matrix (Fin n) (Fin n) F) =
    (A : Matrix (Fin n) (Fin n) F) * (suMat σ n g).map φ
  conj : ∀ g, Φ (α g) = y * Φ g * y⁻¹

theorem IsSemilinearLift.comp {K : Type*} [Group K] {Φ : SU σ n →* K} {y₁ y₂ : K}
    {A₁ A₂ : GL (Fin n) F} {φ₁ φ₂ : F ≃+* F} {α₁ α₂ : SU σ n →* SU σ n}
    (h₁ : IsSemilinearLift Φ y₁ A₁ φ₁ α₁) (h₂ : IsSemilinearLift Φ y₂ A₂ φ₂ α₂) :
    IsSemilinearLift Φ (y₁ * y₂) (A₁ * glAut φ₁ A₂) (φ₂.trans φ₁) (α₁.comp α₂) where
  isometry := by
    have h₂' := congrArg (fun M : Matrix (Fin n) (Fin n) F => M.map φ₁) h₂.isometry
    simp only [Matrix.map_mul] at h₂'
    rw [map_conjTr φ₁ h₁.comm (A₂ : Matrix (Fin n) (Fin n) F), map_antidiag φ₁ n] at h₂'
    rw [Units.val_mul, coe_glAut, conjTr_mul]
    calc
      conjTr σ ((A₂ : Matrix (Fin n) (Fin n) F).map φ₁) *
          conjTr σ (A₁ : Matrix (Fin n) (Fin n) F) * antidiag n *
            ((A₁ : Matrix (Fin n) (Fin n) F) *
              (A₂ : Matrix (Fin n) (Fin n) F).map φ₁) =
        conjTr σ ((A₂ : Matrix (Fin n) (Fin n) F).map φ₁) *
          (conjTr σ (A₁ : Matrix (Fin n) (Fin n) F) * antidiag n *
            (A₁ : Matrix (Fin n) (Fin n) F)) *
              (A₂ : Matrix (Fin n) (Fin n) F).map φ₁ := by
          simp only [Matrix.mul_assoc]
      _ = conjTr σ ((A₂ : Matrix (Fin n) (Fin n) F).map φ₁) * antidiag n *
            (A₂ : Matrix (Fin n) (Fin n) F).map φ₁ := by rw [h₁.isometry]
      _ = antidiag n := h₂'
  comm := by
    intro c
    change φ₁ (φ₂ (σ c)) = σ (φ₁ (φ₂ c))
    rw [h₂.comm c, h₁.comm (φ₂ c)]
  mat := by
    intro g
    have h₂' := congrArg (fun M : Matrix (Fin n) (Fin n) F => M.map φ₁) (h₂.mat g)
    simp only [Matrix.map_mul] at h₂'
    rw [show ((suMat σ n g).map φ₂).map φ₁ = (suMat σ n g).map (φ₂.trans φ₁) from rfl] at h₂'
    rw [Units.val_mul, coe_glAut]
    calc
      suMat σ n (α₁ (α₂ g)) * ((A₁ : Matrix (Fin n) (Fin n) F) *
          (A₂ : Matrix (Fin n) (Fin n) F).map φ₁) =
        (suMat σ n (α₁ (α₂ g)) * (A₁ : Matrix (Fin n) (Fin n) F)) *
          (A₂ : Matrix (Fin n) (Fin n) F).map φ₁ := by
          simp only [Matrix.mul_assoc]
      _ = ((A₁ : Matrix (Fin n) (Fin n) F) *
            (suMat σ n (α₂ g)).map φ₁) *
              (A₂ : Matrix (Fin n) (Fin n) F).map φ₁ := by rw [h₁.mat (α₂ g)]
      _ = (A₁ : Matrix (Fin n) (Fin n) F) *
            ((suMat σ n (α₂ g)).map φ₁ *
              (A₂ : Matrix (Fin n) (Fin n) F).map φ₁) := by
          simp only [Matrix.mul_assoc]
      _ = (A₁ : Matrix (Fin n) (Fin n) F) *
            ((A₂ : Matrix (Fin n) (Fin n) F).map φ₁ *
              (suMat σ n g).map (φ₂.trans φ₁)) := by rw [h₂']
      _ = ((A₁ : Matrix (Fin n) (Fin n) F) *
            (A₂ : Matrix (Fin n) (Fin n) F).map φ₁) *
              (suMat σ n g).map (φ₂.trans φ₁) := by
          simp only [Matrix.mul_assoc]
  conj := by
    intro g
    change Φ (α₁ (α₂ g)) = y₁ * y₂ * Φ g * (y₁ * y₂)⁻¹
    rw [h₁.conj (α₂ g), h₂.conj g, _root_.mul_inv_rev]
    group

theorem IsSemilinearLift.smul {K : Type*} [Group K] {Φ : SU σ n →* K} {y : K}
    {A : GL (Fin n) F} {φ : F ≃+* F} {α : SU σ n →* SU σ n} (hL : IsSemilinearLift Φ y A φ α)
    (u : Fˣ) (hu : σ (u : F) * (u : F) = 1) :
    IsSemilinearLift Φ y (Matrix.GeneralLinearGroup.scalar (Fin n) u * A) φ α where
  isometry := by
    have hsc := conjTr_scalar_mul_antidiag_mul_scalar (σ := σ) (n := n) (u : F)
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, conjTr_mul]
    calc
      conjTr σ (A : Matrix (Fin n) (Fin n) F) *
          conjTr σ (Matrix.scalar (Fin n) (u : F)) * antidiag n *
            (Matrix.scalar (Fin n) (u : F) * (A : Matrix (Fin n) (Fin n) F)) =
        conjTr σ (A : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (Matrix.scalar (Fin n) (u : F)) * antidiag n *
            Matrix.scalar (Fin n) (u : F)) * (A : Matrix (Fin n) (Fin n) F) := by
          simp only [Matrix.mul_assoc]
      _ = conjTr σ (A : Matrix (Fin n) (Fin n) F) *
            ((σ (u : F) * (u : F)) • antidiag n) *
              (A : Matrix (Fin n) (Fin n) F) := by rw [hsc]
      _ = (σ (u : F) * (u : F)) •
            (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
              (A : Matrix (Fin n) (Fin n) F)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = antidiag n := by rw [hu, hL.isometry, one_smul]
  comm := hL.comm
  mat := by
    intro g
    have hscalar : (((Matrix.GeneralLinearGroup.scalar (Fin n) u * A : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F)) = (u : F) • (A : Matrix (Fin n) (Fin n) F) := by
      rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
    rw [hscalar, Matrix.mul_smul, Matrix.smul_mul, hL.mat g]
  conj := hL.conj

private theorem alpha_eq_of_commute_transvection [CharP F 2] {K : Type*} [Group K]
    {Φ : SU σ n →* K} {y : K} {A : GL (Fin n) F} {φ : F ≃+* F}
    {α : SU σ n →* SU σ n} (hL : IsSemilinearLift Φ y A φ α)
    (hker : Φ.ker ≤ Subgroup.center (SU σ n)) {u : Fin n → F}
    (huu : uForm σ u u = 0) {t : SU σ n} (ht : suMat σ n t = uTrans σ u 1)
    (hyt : y * Φ t = Φ t * y) : α t = t := by
  have htt : t * t = 1 := by
    apply suMat_injective σ
    rw [map_mul, ht, uTrans_mul_uTrans σ huu, map_one]
    rw [show (1 : F) + 1 = 0 from CharTwo.add_self_eq_zero 1, uTrans_zero]
  have hαtt : α t * α t = 1 := by
    rw [← map_mul, htt, map_one]
  let z : SU σ n := α t * t⁻¹
  have hzmem : z ∈ Φ.ker := by
    rw [MonoidHom.mem_ker]
    change Φ (α t * t⁻¹) = 1
    rw [map_mul, map_inv, hL.conj t, hyt]
    group
  have hzc : z ∈ Subgroup.center (SU σ n) := hker hzmem
  have hzt : α t = z * t := by
    rw [show z = α t * t⁻¹ from rfl, mul_assoc, inv_mul_cancel, mul_one]
  have hcz : z * t = t * z := (Subgroup.mem_center_iff.mp hzc t).symm
  have hcommt : α t * t = t * α t := by
    rw [hzt]
    calc (z * t) * t = (t * z) * t := by rw [hcz]
      _ = t * (z * t) := by rw [mul_assoc]
  have hz2 : z ^ 2 = 1 := by
    have hzinv : α t * t⁻¹ = t⁻¹ * α t :=
      (show Commute (α t) t from hcommt).inv_right.eq
    have htinvt : t⁻¹ * t⁻¹ = 1 := by rw [← _root_.mul_inv_rev, htt, inv_one]
    calc z ^ 2 = z * z := pow_two z
      _ = (α t * t⁻¹) * (α t * t⁻¹) := rfl
      _ = α t * (t⁻¹ * α t) * t⁻¹ := by simp only [mul_assoc]
      _ = α t * (α t * t⁻¹) * t⁻¹ := by rw [← hzinv]
      _ = (α t * α t) * (t⁻¹ * t⁻¹) := by simp only [mul_assoc]
      _ = 1 := by rw [hαtt, htinvt, mul_one]
  have hz1 : z = 1 := CFSG.StandardType.eq_one_of_mem_center_SU_of_sq_eq_one σ hzc hz2
  have h : α t * t⁻¹ = 1 := hz1
  calc α t = (α t * t⁻¹) * t := by group
    _ = 1 * t := by rw [h]
    _ = t := by rw [one_mul]

theorem IsSemilinearLift.exists_smul [CharP F 2] {K : Type*} [Group K] {Φ : SU σ n →* K}
    {y : K} {A : GL (Fin n) F} {φ : F ≃+* F} {α : SU σ n →* SU σ n}
    (hL : IsSemilinearLift Φ y A φ α) (hker : Φ.ker ≤ Subgroup.center (SU σ n))
    {u : Fin n → F} (huu : uForm σ u u = 0) {t : SU σ n} (ht : suMat σ n t = uTrans σ u 1)
    (hyt : y * Φ t = Φ t * y) :
    ∃ μ : F, (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (u i)) = μ • u := by
  have hαt : α t = t := alpha_eq_of_commute_transvection hL hker huu ht hyt
  have hmat : uTrans σ u 1 * (A : Matrix (Fin n) (Fin n) F) =
      (A : Matrix (Fin n) (Fin n) F) *
        uTrans σ (fun i => φ (u i)) 1 := by
    have h := hL.mat t
    rw [hαt, ht, map_uTrans φ hL.comm u 1, map_one] at h
    exact h
  have heq : uTrans σ u 1 * (A : Matrix (Fin n) (Fin n) F) =
      uTrans σ ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (u i)) 1 *
        (A : Matrix (Fin n) (Fin n) F) := by
    rw [hmat, mul_uTrans_of_isometry hL.isometry]
  have hAinv : (A : Matrix (Fin n) (Fin n) F) *
      ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F) = 1 := by
    simpa using congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F))
      (mul_inv_cancel A)
  have hcancel : uTrans σ u 1 =
      uTrans σ ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (u i)) 1 := by
    calc uTrans σ u 1 = uTrans σ u 1 * 1 := by rw [mul_one]
      _ = uTrans σ u 1 * ((A : Matrix (Fin n) (Fin n) F) *
            ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F)) := by rw [hAinv]
      _ = (uTrans σ u 1 * (A : Matrix (Fin n) (Fin n) F)) *
            ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F) := by
          simp only [Matrix.mul_assoc]
      _ = (uTrans σ ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (u i)) 1 *
            (A : Matrix (Fin n) (Fin n) F)) *
              ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F) := by rw [heq]
      _ = uTrans σ ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (u i)) 1 *
            ((A : Matrix (Fin n) (Fin n) F) *
              ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F)) := by
          simp only [Matrix.mul_assoc]
      _ = uTrans σ ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (u i)) 1 * 1 := by
          rw [hAinv]
      _ = uTrans σ ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (u i)) 1 := by
          rw [mul_one]
  have hnil : uNil σ u =
      uNil σ ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (u i)) := by
    have h := hcancel
    simp only [uTrans, one_smul] at h
    exact add_left_cancel h
  obtain ⟨m, hm⟩ := exists_eq_smul_of_uNil_eq (σ := σ) (l := (1 : F))
    (by simpa using hnil)
  by_cases hu0 : u = 0
  · refine ⟨0, ?_⟩
    have hzero : (fun i => φ (u i)) = 0 := by funext i; simp [hu0]
    rw [hzero, mulVec_zero, zero_smul]
  · have hm0 : m ≠ 0 := fun h => hu0 (by rw [hm, h, zero_smul])
    refine ⟨m⁻¹, ?_⟩
    calc (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (u i)) =
        m⁻¹ • (m • ((A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (u i)))) := by
          rw [smul_smul, inv_mul_cancel₀ hm0, one_smul]
      _ = m⁻¹ • u := by rw [← hm]

theorem exists_scalar_of_mem_center [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {z : SU (unitaryInvolution F 2 f) n}
    (hz : z ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    ∃ c : F, suMat (unitaryInvolution F 2 f) n z = c • 1 := by
  obtain ⟨c, hc⟩ := CFSG.StandardType.InnerDiagSU.exists_scalar_of_mem_center (f := f) hF hn
    (fun hq' => hq ⟨congrArg Prod.fst hq', congrArg Prod.snd hq'⟩) hz
  refine ⟨c, ?_⟩
  rw [show suMat (unitaryInvolution F 2 f) n z =
    CFSG.LieType.Universal.Unitary.SUExtras.mat (unitaryInvolution F 2 f) n z from rfl,
    hc, Matrix.smul_one_eq_diagonal]
  rfl

private theorem ker_quotient_comp_subgroupCongr {p f : ℕ} {K : Type} [Field K] {m : ℕ}
    (h : UnitaryFieldData p f K) {C : GL (Fin m) K} (hCg : IsPrimeFormGram C)
    (hn : 3 ≤ m) (hq : ¬(m = 3 ∧ p ^ f = 2)) {H : Subgroup (GL (Fin m) K)}
    (hSU : H = gramSU h (C : Matrix (Fin m) (Fin m) K)) :
    ((QuotientGroup.mk' (normOneScalars h (gramSU h (C : Matrix (Fin m) (Fin m) K)) m)).comp
      (MulEquiv.subgroupCongr hSU).toMonoidHom).ker = Subgroup.center H := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff,
    ← CFSG.SeitzReduction.F4Pilot.center_gramSU_eq_normOneScalars h hCg hn hq]
  constructor
  · intro hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    apply (MulEquiv.subgroupCongr hSU).injective
    rw [map_mul, map_mul]
    exact hx ((MulEquiv.subgroupCongr hSU) g)
  · intro hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨g, rfl⟩ := (MulEquiv.subgroupCongr hSU).surjective y
    change (MulEquiv.subgroupCongr hSU) g * (MulEquiv.subgroupCongr hSU) x =
      (MulEquiv.subgroupCongr hSU) x * (MulEquiv.subgroupCongr hSU) g
    rw [← map_mul, ← map_mul, hx g]

private theorem exists_semilinear_data [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (h : UnitaryFieldData 2 f F) {C : GL (Fin n) F} (hCg : IsPrimeFormGram C)
    (hSU : SU (unitaryInvolution F 2 f) n = gramSU h (C : Matrix (Fin n) (Fin n) F))
    {K : Type*} [Group K] {Φ : SU (unitaryInvolution F 2 f) n →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    (hN : Φ.range.Normal) (y : K) :
    ∃ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) F)) (φ : F ≃+* F)
      (α : SU (unitaryInvolution F 2 f) n →* SU (unitaryInvolution F 2 f) n),
      (∀ g, suMat (unitaryInvolution F 2 f) n (α g) =
        ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (suMat (unitaryInvolution F 2 f) n g).map φ *
            ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F)) ∧
      (∀ g, Φ (α g) = y * Φ g * y⁻¹) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Φ.range.Normal := hN
  let E : SU (unitaryInvolution F 2 f) n ≃*
      gramSU h (C : Matrix (Fin n) (Fin n) F) := MulEquiv.subgroupCongr hSU
  let π : SU (unitaryInvolution F 2 f) n →*
      primeFormP h (C : Matrix (Fin n) (Fin n) F) :=
    (QuotientGroup.mk' (normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) F)) n)).comp
      E.toMonoidHom
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp E.surjective
  have hπker : π.ker = Subgroup.center (SU (unitaryInvolution F 2 f) n) :=
    ker_quotient_comp_subgroupCongr h hCg hn hq hSU
  haveI : Group.IsPerfect (SU (unitaryInvolution F 2 f) n) :=
    (isQuasisimple_SU hF hn
      (fun hq' => hq ⟨congrArg Prod.fst hq', congrArg Prod.snd hq'⟩)).1
  let θ : SU (unitaryInvolution F 2 f) n →* Φ.range := Φ.rangeRestrict
  have hθker : θ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n) := by
    rw [show θ = Φ.rangeRestrict from rfl, MonoidHom.ker_rangeRestrict]
    exact hker
  have hyN : y ∈ Subgroup.normalizer (Φ.range : Set K) := by
    rw [Subgroup.normalizer_eq_top (H := Φ.range)]
    exact Subgroup.mem_top y
  let τ : MulAut Φ.range := Φ.range.normalizerMonoidHom ⟨y, hyN⟩
  obtain ⟨β, hβ, -⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.exists_mulEquiv_of_central_cover hπ hπker
      (MonoidHom.rangeRestrict_surjective Φ) hθker τ
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hCg hn hq β
  let α : SU (unitaryInvolution F 2 f) n →* SU (unitaryInvolution F 2 f) n :=
    E.symm.toMonoidHom.comp
      ((primeFormConjSU h (C : Matrix (Fin n) (Fin n) F) A).toMonoidHom.comp
        ((primeFormFieldSU h hCg φ).toMonoidHom.comp E.toMonoidHom))
  have hαπ : ∀ g, π (α g) = β (π g) := by
    intro g
    rw [← hAφ, primeFormPsi_apply, MulAut.mul_apply]
    change (((primeFormConjSU h (C : Matrix (Fin n) (Fin n) F) A
        (primeFormFieldSU h hCg φ (E g)) : gramSU h (C : Matrix (Fin n) (Fin n) F))) :
          primeFormP h (C : Matrix (Fin n) (Fin n) F)) =
      primeFormConjHom h (C : Matrix (Fin n) (Fin n) F) A
        (primeFormFieldHom h hCg φ
          (((E g : gramSU h (C : Matrix (Fin n) (Fin n) F)) :
            primeFormP h (C : Matrix (Fin n) (Fin n) F))))
    rw [← primeFormConjAut_mk h (C : Matrix (Fin n) (Fin n) F) A
        (primeFormFieldSU h hCg φ (E g)),
      ← primeFormFieldAut_mk h hCg φ (E g)]
    rfl
  have hαcoe : ∀ g, suMat (unitaryInvolution F 2 f) n (α g) =
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (suMat (unitaryInvolution F 2 f) n g).map φ *
          ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F) := by
    intro g
    have hα : E (α g) = primeFormConjSU h (C : Matrix (Fin n) (Fin n) F) A
        (primeFormFieldSU h hCg φ (E g)) := by
      simp [α]
    have h := congrArg (fun x : gramSU h (C : Matrix (Fin n) (Fin n) F) =>
      ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) hα
    simpa [E, MulEquiv.subgroupCongr_apply, MulEquiv.subgroupCongr_symm_apply,
      coe_glAut, primeFormConjSU, primeFormFieldSU, suMat_apply] using h
  refine ⟨A, φ, α, hαcoe, fun g => ?_⟩
  have h := congrArg Subtype.val (hβ α hαπ g)
  change Φ (α g) =
    ↑((Φ.range.normalizerMonoidHom ⟨y, hyN⟩) (Φ.rangeRestrict g)) at h
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
  simpa using h

private theorem isSemilinearLift_of_primeForm {f : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ}
    (h : UnitaryFieldData 2 f F) {C : GL (Fin n) F}
    (hCa : (C : Matrix (Fin n) (Fin n) F) = antidiag n)
    {K : Type*} [Group K] {Φ : SU (unitaryInvolution F 2 f) n →* K} {y : K}
    {A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) F)} {φ : F ≃+* F}
    {α : SU (unitaryInvolution F 2 f) n →* SU (unitaryInvolution F 2 f) n}
    (hmat : ∀ g, suMat (unitaryInvolution F 2 f) n (α g) =
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (suMat (unitaryInvolution F 2 f) n g).map φ *
          ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F))
    (hconj : ∀ g, Φ (α g) = y * Φ g * y⁻¹) :
    IsSemilinearLift Φ y (A : GL (Fin n) F) φ α where
  isometry := by
    have hA := (mem_primeFormUnitary (h := h) (C := (C : Matrix (Fin n) (Fin n) F))).mp A.2
    calc
      conjTr (unitaryInvolution F 2 f) ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          antidiag n * ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).map h.bar)ᵀ *
          (C : Matrix (Fin n) (Fin n) F) *
            ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          rw [conjTr, CFSG.StandardType.RootDetectSU.map_eq_map_bar h, ← hCa]
      _ = (C : Matrix (Fin n) (Fin n) F) := hA
      _ = antidiag n := hCa
  comm := by
    intro c
    rw [← CFSG.StandardType.RootDetectSU.bar_eq h c, map_bar_comm h φ c,
      CFSG.StandardType.RootDetectSU.bar_eq h (φ c)]
  mat := by
    intro g
    rw [hmat g]
    have hAinv : ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F) *
        ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
      have := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F))
        (inv_mul_cancel (A : GL (Fin n) F))
      simpa using this
    calc
      (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (suMat (unitaryInvolution F 2 f) n g).map φ *
            ((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F)) *
              ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (suMat (unitaryInvolution F 2 f) n g).map φ) *
          (((A : GL (Fin n) F)⁻¹ : Matrix (Fin n) (Fin n) F) *
            ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          simp only [Matrix.mul_assoc]
      _ = (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (suMat (unitaryInvolution F 2 f) n g).map φ) * 1 := by rw [hAinv]
      _ = ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (suMat (unitaryInvolution F 2 f) n g).map φ := by rw [Matrix.mul_one]
  conj := hconj

theorem exists_isSemilinearLift [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {K : Type*} [Group K] {Φ : SU (unitaryInvolution F 2 f) n →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) (hN : Φ.range.Normal)
    (y : K) :
    ∃ (A : GL (Fin n) F) (φ : F ≃+* F)
      (α : SU (unitaryInvolution F 2 f) n →* SU (unitaryInvolution F 2 f) n),
      IsSemilinearLift Φ y A φ α := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let h : UnitaryFieldData 2 f F := CFSG.StandardType.RootDetectSU.unitaryFieldData_two hF hf
  let C : GL (Fin n) F := ⟨antidiag n, antidiag n, antidiag_mul_antidiag, antidiag_mul_antidiag⟩
  have hCa : (C : Matrix (Fin n) (Fin n) F) = antidiag n := rfl
  have hCg : IsPrimeFormGram C :=
    CFSG.StandardType.RootDetectSU.isPrimeFormGram_of_eq_antidiag hCa
  have hSU : SU (unitaryInvolution F 2 f) n =
      gramSU h (C : Matrix (Fin n) (Fin n) F) := by
    rw [hCa]
    exact CFSG.StandardType.RootDetectSU.SU_eq_gramSU_antidiag h
  obtain ⟨A, φ, α, hmat, hconj⟩ :=
    exists_semilinear_data hF hn hq h hCg hSU hker hN y
  exact ⟨(A : GL (Fin n) F), φ, α, isSemilinearLift_of_primeForm h hCa hmat hconj⟩

end ModelRank

end CFSG.Timmesfeld.Transvection
