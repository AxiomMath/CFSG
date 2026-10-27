module

public import CFSG.LocalAnalysis.StandardType.GGPSLGraphDefs

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private noncomputable def pslB0_A' {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (A : GL (Fin n) K) : GL (Fin n) K :=
  A * SpecialLinearGroup.toGL (AutPSL.revSL (n := n) (K := K))

private lemma pslB0_inv_inv_coe {n : ℕ} {K : Type} [Field K] (A' : GL (Fin n) K) :
    (((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))⁻¹ =
      (A' : Matrix (Fin n) (Fin n) K) := by
  rw [← GeneralLinearGroup.coe_inv, inv_inv]

private lemma pslB0_inverseTranspose_inv_coe {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ((GeneralLinearGroup.inverseTranspose B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B : Matrix (Fin n) (Fin n) K))ᵀ := by
  rw [GeneralLinearGroup.coe_inverseTranspose, inv_inv]

private lemma pslB0_formAdj_eq {n : ℕ} {K : Type} [Field K] (A' : GL (Fin n) K)
    (X : Matrix (Fin n) (Fin n) K) :
    formAdj (RingHom.id K) (((A'⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) X =
      (A' : Matrix (Fin n) (Fin n) K) * Xᵀ *
        (((A'⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
  have hmap : X.map (RingHom.id K) = X := by ext i j; rfl
  rw [formAdj, hmap, pslB0_inv_inv_coe]

private lemma pslB0_alpha_eq {n : ℕ} {K : Type} [Field K] [CharP K 2] (A : GL (Fin n) K) :
    pslAlpha A = conjAut n K (pslB0_A' A) * dualAut n K := by
  simp only [pslAlpha, AutPSL.graphAut, pslB0_A']
  rw [← mul_assoc, ← map_mul]

private lemma pslB0_proj_eq_scalar {n : ℕ} {K : Type} [Field K]
    {g h : SpecialLinearGroup (Fin n) K} (hh : proj n K g = proj n K h) :
    ∃ c : Kˣ, (g : Matrix (Fin n) (Fin n) K) = (c : K) • (h : Matrix (Fin n) (Fin n) K) := by
  have h1 : proj n K (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hh, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h1)
  refine ⟨c, ?_⟩
  have hmul : (g : Matrix (Fin n) (Fin n) K) * ((h⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (c : K) • 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  have hh_inv : ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (h : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_mul, h.prop, one_smul]
  calc (g : Matrix (Fin n) (Fin n) K)
      = (g : Matrix (Fin n) (Fin n) K) * 1 := (Matrix.mul_one _).symm
    _ = (g : Matrix (Fin n) (Fin n) K) * (((h⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K)) := by rw [hh_inv]
    _ = ((g : Matrix (Fin n) (Fin n) K) * ((h⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) * (h : Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.mul_assoc]
    _ = ((c : K) • 1) * (h : Matrix (Fin n) (Fin n) K) := by rw [hmul]
    _ = (c : K) • (h : Matrix (Fin n) (Fin n) K) := by rw [Matrix.smul_mul, Matrix.one_mul]

private lemma pslB0_conjAut_eq_one_scalar {n : ℕ} {K : Type} [Field K] [Finite K]
    (hn : 3 ≤ n) (M : GL (Fin n) K)
    (hM : ∀ g : SpecialLinearGroup (Fin n) K, conjAut n K M (proj n K g) = proj n K g) :
    ∃ z : Kˣ, (M : Matrix (Fin n) (Fin n) K) = (z : K) • 1 := by
  have h1 : conjAut n K M * fieldAut n K (1 : K ≃+* K) = 1 := by
    rw [map_one, mul_one]
    ext x
    obtain ⟨g, rfl⟩ := proj_surjective n K x
    exact hM g
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn M 1 h1
  refine ⟨c, ?_⟩
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

private lemma pslB0_conj_eq_scalar_mul {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) {M N : GL (Fin n) K} (h : conjAut n K M = conjAut n K N) :
    ∃ z : Kˣ, (M : Matrix (Fin n) (Fin n) K) = (z : K) • (N : Matrix (Fin n) (Fin n) K) := by
  have h1 : conjAut n K (M * N⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨z, hz⟩ := pslB0_conjAut_eq_one_scalar hn (M * N⁻¹)
    (fun g => by rw [h1, MulAut.one_apply])
  refine ⟨z, ?_⟩
  have hz' : (M : Matrix (Fin n) (Fin n) K) * ((N⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (z : K) • 1 := by
    rw [← GeneralLinearGroup.coe_mul, hz]
  calc (M : Matrix (Fin n) (Fin n) K)
      = (M : Matrix (Fin n) (Fin n) K) * 1 := (Matrix.mul_one _).symm
    _ = (M : Matrix (Fin n) (Fin n) K) * (((N⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * (N : Matrix (Fin n) (Fin n) K)) := by
        rw [← GeneralLinearGroup.coe_mul, inv_mul_cancel, GeneralLinearGroup.coe_one]
    _ = ((M : Matrix (Fin n) (Fin n) K) * ((N⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) * (N : Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.mul_assoc]
    _ = ((z : K) • 1) * (N : Matrix (Fin n) (Fin n) K) := by rw [hz']
    _ = (z : K) • (N : Matrix (Fin n) (Fin n) K) := by rw [Matrix.smul_mul, Matrix.one_mul]

private lemma pslB0_alpha_conj {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (A B : GL (Fin n) K) :
    pslAlpha A * conjAut n K B * (pslAlpha A)⁻¹ =
      conjAut n K (pslB0_A' A * GeneralLinearGroup.inverseTranspose B * (pslB0_A' A)⁻¹) := by
  have htr := standard_automorphism_transport (K := K) (n := n)
  have hdual : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_left htr.2.2.2.1
  rw [pslB0_alpha_eq A]
  rw [show (conjAut n K (pslB0_A' A) * dualAut n K) * conjAut n K B *
      (conjAut n K (pslB0_A' A) * dualAut n K)⁻¹ =
      conjAut n K (pslB0_A' A) * (dualAut n K * conjAut n K B * dualAut n K) *
        (conjAut n K (pslB0_A' A))⁻¹ by
    rw [_root_.mul_inv_rev, hdual]; group]
  rw [htr.2.2.2.2.1 B, ← map_inv, ← map_mul, ← map_mul]

private lemma pslB0_symm {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) (A : GL (Fin n) K) (hα2 : pslAlpha A * pslAlpha A = 1) :
    ((pslB0_A' A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      ((pslB0_A' A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have htr := standard_automorphism_transport (K := K) (n := n)
  have hM : conjAut n K (pslB0_A' A * GeneralLinearGroup.inverseTranspose (pslB0_A' A)) = 1 := by
    have h1 : pslAlpha A * pslAlpha A =
        conjAut n K (pslB0_A' A * GeneralLinearGroup.inverseTranspose (pslB0_A' A)) := by
      rw [pslB0_alpha_eq A]
      rw [show (conjAut n K (pslB0_A' A) * dualAut n K) *
          (conjAut n K (pslB0_A' A) * dualAut n K) =
          conjAut n K (pslB0_A' A) * (dualAut n K * conjAut n K (pslB0_A' A) * dualAut n K)
            by group]
      rw [htr.2.2.2.2.1 (pslB0_A' A), ← map_mul]
    rw [← h1]
    exact hα2
  obtain ⟨z, hz⟩ := pslB0_conjAut_eq_one_scalar hn _
    (fun g => by rw [hM, MulAut.one_apply])
  have hAt : (pslB0_A' A : Matrix (Fin n) (Fin n) K) =
      (z : K) • ((pslB0_A' A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
    have h1 : (pslB0_A' A : Matrix (Fin n) (Fin n) K) *
        ((((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹)ᵀ = (z : K) • 1 := by
      rw [← hz, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_inverseTranspose,
        GeneralLinearGroup.coe_inv]
    have hMM : ((((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹)ᵀ *
        (((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← GeneralLinearGroup.coe_inv,
        ← GeneralLinearGroup.coe_mul, mul_inv_cancel, GeneralLinearGroup.coe_one,
        Matrix.transpose_one]
    calc (pslB0_A' A : Matrix (Fin n) (Fin n) K)
        = (pslB0_A' A : Matrix (Fin n) (Fin n) K) * 1 := (Matrix.mul_one _).symm
      _ = (pslB0_A' A : Matrix (Fin n) (Fin n) K) *
            (((((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹)ᵀ *
              (((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)ᵀ) := by rw [hMM]
      _ = ((pslB0_A' A : Matrix (Fin n) (Fin n) K) *
            ((((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹)ᵀ) *
              (((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)ᵀ := by
          rw [Matrix.mul_assoc]
      _ = ((z : K) • 1) *
            (((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)ᵀ := by rw [h1]
      _ = (z : K) • (((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)ᵀ := by
          rw [Matrix.smul_mul, Matrix.one_mul]
  have hAt' : ((pslB0_A' A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      (z : K) • (pslB0_A' A : Matrix (Fin n) (Fin n) K) := by
    have := congrArg Matrix.transpose hAt
    simpa [Matrix.transpose_smul] using this
  have hAeq : (pslB0_A' A : Matrix (Fin n) (Fin n) K) =
      (z : K) ^ 2 • (pslB0_A' A : Matrix (Fin n) (Fin n) K) := by
    calc (pslB0_A' A : Matrix (Fin n) (Fin n) K)
        = (z : K) • ((pslB0_A' A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := hAt
      _ = (z : K) • ((z : K) • (pslB0_A' A : Matrix (Fin n) (Fin n) K)) := by rw [hAt']
      _ = (z : K) ^ 2 • (pslB0_A' A : Matrix (Fin n) (Fin n) K) := by rw [smul_smul, sq]
  have hz2 : (z : K) ^ 2 = 1 := by
    have h1 : (((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹ *
        (pslB0_A' A : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← GeneralLinearGroup.coe_inv, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
        GeneralLinearGroup.coe_one]
    have h2 : (1 : Matrix (Fin n) (Fin n) K) = (z : K) ^ 2 • 1 := by
      calc (1 : Matrix (Fin n) (Fin n) K)
          = (((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹ *
              (pslB0_A' A : Matrix (Fin n) (Fin n) K) := h1.symm
        _ = (((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹ *
              ((z : K) ^ 2 • (pslB0_A' A : Matrix (Fin n) (Fin n) K)) :=
            congrArg (fun X => (((pslB0_A' A : GL (Fin n) K)) :
              Matrix (Fin n) (Fin n) K)⁻¹ * X) hAeq
        _ = (z : K) ^ 2 • ((((pslB0_A' A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹ *
              (pslB0_A' A : Matrix (Fin n) (Fin n) K)) := by rw [Matrix.mul_smul]
        _ = (z : K) ^ 2 • 1 := by rw [h1]
    have h00 := congrFun (congrFun h2 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa [Matrix.smul_apply] using h00.symm
  have hz1 : z = 1 := by
    have hz2u : z ^ 2 = 1 := by
      apply Units.ext
      simpa using hz2
    have hdvd2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2u
    have hdvdK : orderOf z ∣ Nat.card Kˣ :=
      orderOf_dvd_of_pow_eq_one (pow_card_eq_one' (x := z))
    have hcop : Nat.Coprime 2 (Nat.card Kˣ) :=
      Nat.coprime_two_left.mpr (AutPSL.odd_card_units (K := K))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdK)
  rw [hAt', hz1, Units.val_one, one_smul]

private lemma pslB0_odd {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) (B : GL (Fin n) K) (h : Odd (orderOf (conjAut n K B))) :
    Odd (orderOf B) := by
  set m := orderOf (conjAut n K B) with hm
  rw [hm] at h
  have hBm : conjAut n K (B ^ m) = 1 := by
    rw [map_pow, hm, pow_orderOf_eq_one]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (B ^ m) 1
    (by rw [hBm, map_one, mul_one])
  have hpow : B ^ (m * Nat.card Kˣ) = 1 := by
    rw [pow_mul, ← hc, ← map_pow, pow_card_eq_one', map_one]
  exact Odd.of_dvd_nat (h.mul (AutPSL.odd_card_units (K := K)))
    (orderOf_dvd_of_pow_eq_one hpow)

private lemma pslB0_star_mul {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) (A B : GL (Fin n) K)
    (hcomm : pslAlpha A * conjAut n K B = conjAut n K B * pslAlpha A) :
    ∃ c : Kˣ,
      formAdj (RingHom.id K) (((pslB0_A' A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
        (c : K) • 1 := by
  have hcomm' : conjAut n K (pslB0_A' A * GeneralLinearGroup.inverseTranspose B *
      (pslB0_A' A)⁻¹) = conjAut n K B := by
    rw [← pslB0_alpha_conj A B, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨z, hz⟩ := pslB0_conj_eq_scalar_mul hn hcomm'
  have hFY : (pslB0_A' A * GeneralLinearGroup.inverseTranspose B⁻¹ * (pslB0_A' A)⁻¹) *
      (pslB0_A' A * GeneralLinearGroup.inverseTranspose B * (pslB0_A' A)⁻¹) = 1 := by
    rw [map_inv]
    group
  have hFB : ((pslB0_A' A * GeneralLinearGroup.inverseTranspose B⁻¹ *
      (pslB0_A' A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = (z : K)⁻¹ • 1 := by
    have h1 : ((pslB0_A' A * GeneralLinearGroup.inverseTranspose B⁻¹ *
        (pslB0_A' A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((z : K) • (B : Matrix (Fin n) (Fin n) K)) = 1 := by
      rw [← hz, ← GeneralLinearGroup.coe_mul, hFY, GeneralLinearGroup.coe_one]
    have h2 : (z : K) • (((pslB0_A' A * GeneralLinearGroup.inverseTranspose B⁻¹ *
        (pslB0_A' A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (B : Matrix (Fin n) (Fin n) K)) = 1 := by
      rw [← Matrix.mul_smul]
      exact h1
    have hzK : (z : K)⁻¹ * (z : K) = 1 := by
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h3 := congrArg (fun X : Matrix (Fin n) (Fin n) K => (z : K)⁻¹ • X) h2
    simpa [smul_smul, hzK, one_smul] using h3
  have hFg : formAdj (RingHom.id K) (((pslB0_A' A)⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) (B : Matrix (Fin n) (Fin n) K) =
      ((pslB0_A' A * GeneralLinearGroup.inverseTranspose B⁻¹ *
        (pslB0_A' A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [pslB0_formAdj_eq, GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul,
      pslB0_inverseTranspose_inv_coe]
  refine ⟨z⁻¹, ?_⟩
  rw [hFg, hFB, Units.val_inv_eq_inv_val]

private lemma pslB0_fix {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (A B : GL (Fin n) K)
    (hfix : ∀ g : projectiveSL n K, conjAut n K B g = g → pslAlpha A g = g) :
    ∀ x ∈ pslChat B, ∃ d : Kˣ,
      formAdj (RingHom.id K) (((pslB0_A' A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          (((x⁻¹ : SpecialLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
        (d : K) • (x : Matrix (Fin n) (Fin n) K) := by
  intro x hx
  have hxB : conjAut n K B (proj n K x) = proj n K x := by
    simpa [pslChat, pslCent] using hx
  have hproj : proj n K (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      n K (pslB0_A' A) ((x⁻¹ : SpecialLinearGroup (Fin n) K).transpose)) = proj n K x := by
    rw [← conjAut_proj, ← dualAut_proj, ← MulAut.mul_apply, ← pslB0_alpha_eq A]
    exact hfix _ hxB
  obtain ⟨d, hd⟩ := pslB0_proj_eq_scalar hproj
  refine ⟨d, ?_⟩
  rw [pslB0_formAdj_eq, ← hd, coe_slConjugation, SpecialLinearGroup.coe_transpose]

theorem pslGraph_setting_of_hyps {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) (A B : GL (Fin n) K)
    (hα2 : pslAlpha A * pslAlpha A = 1)
    (hodd : Odd (orderOf (conjAut n K B)))
    (hcomm : pslAlpha A * conjAut n K B = conjAut n K B * pslAlpha A)
    (hfix : ∀ g : projectiveSL n K, conjAut n K B g = g → pslAlpha A g = g) :
    ∃ G : Matrix (Fin n) (Fin n) K, PSLGraphSetting n K G B := by
  refine ⟨(((pslB0_A' A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ?_⟩
  refine ⟨hn, ?_, ?_, pslB0_odd hn B hodd, pslB0_star_mul hn A B hcomm,
    pslB0_fix A B hfix⟩
  · rw [GeneralLinearGroup.coe_inv, Matrix.transpose_nonsing_inv, pslB0_symm hn A hα2]
  · exact (isUnit_iff_isUnit_det _).mp (pslB0_A' A)⁻¹.isUnit

end CFSG.StandardType
