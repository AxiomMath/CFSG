module

import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open Matrix
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)

private theorem k328r6g_conjTr_diagonal {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (d : Fin n → K) :
    CFSG.LieType.Universal.Unitary.conjTr σ (Matrix.diagonal d) =
      Matrix.diagonal (fun i => σ (d i)) := by
  ext i j
  rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (Ne.symm h), map_zero, if_neg h]

private theorem k328r6g_mem_SUid_of_diagonal {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (d : Fin n → K) (hdet : ∏ i, d i = 1) (hnorm : ∀ i, σ (d i) * d i = 1)
    (z : GL (Fin n) K) (hz : (z : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d) :
    z ∈ SUid σ n := by
  rw [CFSG.LieType.Universal.Unitary.mem_SUid, hz]
  constructor
  · rw [Matrix.det_diagonal]; exact hdet
  · rw [k328r6g_conjTr_diagonal, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => σ (d i) * d i) = fun _ => 1 from funext hnorm, Matrix.diagonal_one]

private theorem k328r6g_herm_smul_of_fix {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (_hσ : ∀ c, σ (σ c) = c) (s : SUid σ n) {a : Fin n → K} (hsa : s • a = a)
    (v : Fin n → K) : herm σ a (s • v) = herm σ a v := by
  have hsinv : s⁻¹ • a = a := by
    calc s⁻¹ • a = s⁻¹ • (s • a) := by rw [hsa]
      _ = (s⁻¹ * s) • a := by rw [smul_smul]
      _ = a := by rw [inv_mul_cancel, one_smul]
  calc herm σ a (s • v) = herm σ (s⁻¹ • a) v := by
        rw [← herm_smul_smul σ s (s⁻¹ • a) v, smul_inv_smul]
    _ = herm σ a v := by rw [hsinv]

private theorem k328r6g_tv_comm_of_fix {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0)
    {c : K} (hc : c + σ c = 0) (s : SUid σ n) (hsa : s • a = a) :
    tv hσ ha hc * s = s * tv hσ ha hc := by
  apply ext_smul
  intro v
  rw [mul_smul, mul_smul, tv_smul, tv_smul, k328r6g_herm_smul_of_fix hσ s hsa v]
  simp only [smul_add]
  rw [smul_comm s (c * herm σ a v) a, hsa]

private def k328r6g_headEmb {K : Type} [Zero K] (u : Fin 3 → K) : Fin 4 → K :=
  ![u 0, u 1, u 2, 0]

private theorem k328r6g_headEmb_apply_three {K : Type} [Zero K] (u : Fin 3 → K) :
    k328r6g_headEmb u 3 = 0 := rfl

private theorem k328r6g_headEmb_single {K : Type} [Zero K] [One K] (j : Fin 3) :
    k328r6g_headEmb (Pi.single j (1 : K)) = Pi.single (Fin.castSucc j) 1 := by
  ext i
  fin_cases i <;> fin_cases j <;> simp [k328r6g_headEmb]

private theorem k328r6g_castSucc_ne_three (i : Fin 3) : (Fin.castSucc i : Fin 4) ≠ 3 := by
  intro h
  have := congrArg Fin.val h
  simp [Fin.castSucc] at this
  omega

private def k328r6g_headEmbLinear (K : Type) [Field K] : (Fin 3 → K) →ₗ[K] (Fin 4 → K) where
  toFun := k328r6g_headEmb
  map_add' u v := by
    ext i; fin_cases i <;> simp [k328r6g_headEmb, Pi.add_apply]
  map_smul' c u := by
    ext i; fin_cases i <;> simp [k328r6g_headEmb, Pi.smul_apply]

@[simp] private theorem k328r6g_headEmbLinear_apply (K : Type) [Field K]
    (u : Fin 3 → K) : (k328r6g_headEmbLinear K) u = k328r6g_headEmb u := rfl

private theorem k328r6g_headEmb_isometry {K : Type} [Field K] (σ : K ≃+* K)
    (u v : Fin 3 → K) :
    herm σ (k328r6g_headEmb u) (k328r6g_headEmb v) = herm σ u v := by
  simp only [herm, k328r6g_headEmb, Fin.sum_univ_four, Fin.sum_univ_three]
  simp [Matrix.cons_val_zero]

private theorem k328r6g_comm_z0_of_head {K : Type} [Field K] {σ : K ≃+* K} {ω : K}
    {z₀ : GL (Fin 4) K}
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![ω, ω, ω, 1])
    (g : SUid σ 4) (hge3 : g • (Pi.single (3 : Fin 4) (1 : K) : Fin 4 → K) =
      Pi.single (3 : Fin 4) (1 : K))
    (hW : ∀ j : Fin 3, (g • k328r6g_headEmb (Pi.single j (1 : K))) 3 = 0) :
    (g : GL (Fin 4) K) * z₀ = z₀ * g := by
  have hcol : ∀ i : Fin 4, i ≠ 3 →
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i 3 = 0 := by
    intro i hi
    have h := congrFun hge3 i
    simp only [smul_def, Matrix.mulVec_single_one] at h
    simpa [Pi.single_apply, hi] using h
  have hrow : ∀ j : Fin 3,
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 (Fin.castSucc j) = 0 := by
    intro j
    have h := hW j
    simp only [k328r6g_headEmb_single, smul_def, Matrix.mulVec_single_one] at h
    exact h
  have h03 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 := hcol 0 (by decide)
  have h13 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 := hcol 1 (by decide)
  have h23 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 := hcol 2 (by decide)
  have h30 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 0 = 0 := hrow 0
  have h31 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 1 = 0 := hrow 1
  have h32 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 2 = 0 := hrow 2
  have hmain : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (z₀ : Matrix (Fin 4) (Fin 4) K) =
      (z₀ : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    simp only [Matrix.mul_apply, hz, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp [h03, h13, h23, h30, h31, h32, mul_comm]
  exact Units.ext hmain

private theorem k328r6g_tv_congr {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} {c : K}
    (ha₁ ha₂ : herm σ a a = 0) (hc : c + σ c = 0) :
    tv hσ ha₁ hc = tv hσ ha₂ hc := by
  apply Subtype.ext
  apply Units.ext
  rfl

private theorem k328r6g_tv_conj {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) (g : SUid σ n) (hga : herm σ (g • a) (g • a) = 0) :
    g * tv hσ ha hc * g⁻¹ = tv hσ hga hc := by
  apply ext_smul
  intro v
  rw [conj_smul_of_tv g (tv hσ ha hc) (tv_smul hσ ha hc) v, tv_smul]

private theorem k328r6g_mul_smul_fix {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (g h : SUid σ n) {a : Fin n → K} {μ ν : K}
    (hg : g • a = μ • a) (hh : h • a = ν • a) :
    (g * h) • a = (μ * ν) • a := by
  rw [mul_smul, hh, smul_comm g ν a, hg, smul_smul, mul_comm]

theorem row6_gen (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 64) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 4) F)
    (hz : (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1])
    (ht : (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1]) :
    GenLeaf (StatedSU 4 8 F) z₀ t₀ := by
  have hF' : Nat.card F = (2 ^ 3) ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_sq (p := 2) (f := 3) hF'
  let σ : F ≃+* F := unitaryInvolution F 2 3
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF'
  have hσinv : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution hF'
  have hω3 : ω ^ 3 = 1 := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
    rw [hω, mul_zero] at h
    exact sub_eq_zero.mp h.symm
  have hσω : σ ω = ω ^ 8 := by
    rw [show σ = unitaryInvolution F 2 3 from rfl, unitaryInvolution_apply]
    norm_num
  have hσω2 : σ (ω ^ 2) = ω ^ 16 := by
    rw [show σ = unitaryInvolution F 2 3 from rfl, unitaryInvolution_apply, ← pow_mul]
    norm_num
  have hω_norm : σ ω * ω = 1 := by
    rw [hσω, ← pow_succ, show 8 + 1 = 3 * 3 by norm_num, pow_mul, hω3, one_pow]
  have hω2_norm : σ (ω ^ 2) * ω ^ 2 = 1 := by
    rw [hσω2, ← pow_add, show 16 + 2 = 3 * 6 by norm_num, pow_mul, hω3, one_pow]
  have hprod_z : ∏ i : Fin 4, ![ω, ω, ω, 1] i = 1 := by
    rw [Fin.prod_univ_four]
    rw [show ![ω, ω, ω, 1] (0 : Fin 4) = ω from rfl,
      show ![ω, ω, ω, 1] (1 : Fin 4) = ω from rfl,
      show ![ω, ω, ω, 1] (2 : Fin 4) = ω from rfl,
      show ![ω, ω, ω, 1] (3 : Fin 4) = 1 from rfl, mul_one]
    have h : ω * ω * ω = ω ^ 3 := by ring
    rw [h, hω3]
  have hprod_t : ∏ i : Fin 4, ![ω, ω ^ 2, 1, 1] i = 1 := by
    rw [Fin.prod_univ_four]
    rw [show ![ω, ω ^ 2, 1, 1] (0 : Fin 4) = ω from rfl,
      show ![ω, ω ^ 2, 1, 1] (1 : Fin 4) = ω ^ 2 from rfl,
      show ![ω, ω ^ 2, 1, 1] (2 : Fin 4) = 1 from rfl,
      show ![ω, ω ^ 2, 1, 1] (3 : Fin 4) = 1 from rfl]
    have h : ω * ω ^ 2 * 1 * 1 = ω ^ 3 := by ring
    rw [h, hω3]
  have hz0_mem : z₀ ∈ SUid σ 4 :=
    k328r6g_mem_SUid_of_diagonal ![ω, ω, ω, 1] hprod_z
      (fun i => by
        fin_cases i
        · exact hω_norm
        · exact hω_norm
        · exact hω_norm
        · simp) z₀ hz
  have ht0_mem : t₀ ∈ SUid σ 4 :=
    k328r6g_mem_SUid_of_diagonal ![ω, ω ^ 2, 1, 1] hprod_t
      (fun i => by
        fin_cases i
        · exact hω_norm
        · exact hω2_norm
        · simp
        · simp) t₀ ht
  let z0' : SUid σ 4 := ⟨z₀, hz0_mem⟩
  let t0' : SUid σ 4 := ⟨t₀, ht0_mem⟩
  have hz0_e : ∀ i : Fin 4,
      z0' • (Pi.single i (1 : F) : Fin 4 → F) = ![ω, ω, ω, 1] i • Pi.single i 1 := by
    intro i
    rw [smul_def, show ((z0' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![ω, ω, ω, 1] from hz, Matrix.diagonal_mulVec_single]
    ext k
    simp [Pi.single_apply]
  have ht0_e : ∀ i : Fin 4,
      t0' • (Pi.single i (1 : F) : Fin 4 → F) = ![ω, ω ^ 2, 1, 1] i • Pi.single i 1 := by
    intro i
    rw [smul_def, show ((t0' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![ω, ω ^ 2, 1, 1] from ht, Matrix.diagonal_mulVec_single]
    ext k
    simp [Pi.single_apply]
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8, ← SUid_eq_statedSU hF' 4]
  let J : Subgroup (GL (Fin 4) F) :=
    SUid σ 4 ⊓ Subgroup.centralizer ({z₀} : Set (GL (Fin 4) F)) ⊔
    SUid σ 4 ⊓ Subgroup.centralizer ({t₀} : Set (GL (Fin 4) F)) ⊔
    SUid σ 4 ⊓ Subgroup.centralizer ({z₀ * t₀} : Set (GL (Fin 4) F)) ⊔
    SUid σ 4 ⊓ Subgroup.centralizer ({z₀ * t₀ ^ 2} : Set (GL (Fin 4) F))
  change J = SUid σ 4
  apply le_antisymm
  · exact sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left) inf_le_left
  ·
    have hS_of_ne : ∀ a, herm σ a a = 0 → a ≠ 0 →
        ∀ (ha : herm σ a a = 0) (c : F) (hc : c + σ c = 0),
          ((tv hσ ha hc : SUid σ 4) : GL (Fin 4) F) ∈ J := by
      let S : Set (Fin 4 → F) :=
        {a | a ≠ 0 ∧ herm σ a a = 0 ∧ ∀ (ha : herm σ a a = 0) (c : F) (hc : c + σ c = 0),
          ((tv hσ ha hc : SUid σ 4) : GL (Fin 4) F) ∈ J}
      have hS_stable : ∀ a ∈ S, ∀ g : SUid σ 4, (g : GL (Fin 4) F) ∈ J → g • a ∈ S := by
        intro a haS g hgJ
        have hga : herm σ (g • a) (g • a) = 0 := by rw [herm_smul_smul, haS.2.1]
        refine ⟨?_, hga, ?_⟩
        · intro h
          exact haS.1 (by
            have := congrArg (fun v => g⁻¹ • v) h
            simpa using this)
        · intro ha' c hc
          have htva : ((tv hσ haS.2.1 hc : SUid σ 4) : GL (Fin 4) F) ∈ J := haS.2.2 haS.2.1 c hc
          have hconj := k328r6g_tv_conj hσ haS.2.1 hc g hga
          have hprod : ((tv hσ hga hc : SUid σ 4) : GL (Fin 4) F) =
              (g : GL (Fin 4) F) * ((tv hσ haS.2.1 hc : SUid σ 4) : GL (Fin 4) F) * g⁻¹ := by
            rw [← hconj]; rfl
          rw [k328r6g_tv_congr hσ ha' hga hc, hprod]
          exact J.mul_mem (J.mul_mem hgJ htva) (J.inv_mem hgJ)
      let s1 : SUid σ 4 := z0' * t0' ^ 2
      let s2 : SUid σ 4 := z0' * t0'
      let s3 : SUid σ 4 := t0'
      have hz0_e0 : z0' • (Pi.single 0 (1 : F) : Fin 4 → F) = ω • Pi.single 0 1 := hz0_e 0
      have hz0_e1 : z0' • (Pi.single 1 (1 : F) : Fin 4 → F) = ω • Pi.single 1 1 := hz0_e 1
      have hz0_e2 : z0' • (Pi.single 2 (1 : F) : Fin 4 → F) = ω • Pi.single 2 1 := hz0_e 2
      have hz0_e3 : z0' • (Pi.single 3 (1 : F) : Fin 4 → F) = (1 : F) • Pi.single 3 1 := by
        rw [hz0_e 3, show ![ω, ω, ω, 1] (3 : Fin 4) = 1 from rfl]
      have ht0_e0 : t0' • (Pi.single 0 (1 : F) : Fin 4 → F) = ω • Pi.single 0 1 := ht0_e 0
      have ht0_e1 : t0' • (Pi.single 1 (1 : F) : Fin 4 → F) = ω ^ 2 • Pi.single 1 1 := ht0_e 1
      have ht0_e2 : t0' • (Pi.single 2 (1 : F) : Fin 4 → F) = (1 : F) • Pi.single 2 1 := by
        rw [ht0_e 2, show ![ω, ω ^ 2, 1, 1] (2 : Fin 4) = 1 from rfl]
      have ht0_e3 : t0' • (Pi.single 3 (1 : F) : Fin 4 → F) = (1 : F) • Pi.single 3 1 := by
        rw [ht0_e 3, show ![ω, ω ^ 2, 1, 1] (3 : Fin 4) = 1 from rfl]
      have hωω2 : ω * ω ^ 2 = 1 := by rw [mul_comm, ← pow_succ, hω3]
      have hs1_e0 : s1 • (Pi.single 0 (1 : F) : Fin 4 → F) = Pi.single 0 1 := by
        have ht2 : t0' ^ 2 • (Pi.single 0 (1 : F) : Fin 4 → F) = ω ^ 2 • Pi.single 0 1 := by
          rw [pow_two, k328r6g_mul_smul_fix t0' t0' ht0_e0 ht0_e0,
            show ω * ω = ω ^ 2 from by ring]
        rw [show s1 = z0' * t0' ^ 2 from rfl, k328r6g_mul_smul_fix z0' (t0' ^ 2) hz0_e0 ht2,
          hωω2, one_smul]
      have hs1_e3 : s1 • (Pi.single 3 (1 : F) : Fin 4 → F) = Pi.single 3 1 := by
        have ht2 : t0' ^ 2 • (Pi.single 3 (1 : F) : Fin 4 → F) = (1 : F) • Pi.single 3 1 := by
          rw [pow_two, k328r6g_mul_smul_fix t0' t0' ht0_e3 ht0_e3, one_mul]
        rw [show s1 = z0' * t0' ^ 2 from rfl, k328r6g_mul_smul_fix z0' (t0' ^ 2) hz0_e3 ht2,
          one_mul, one_smul]
      have hs2_e1 : s2 • (Pi.single 1 (1 : F) : Fin 4 → F) = Pi.single 1 1 := by
        rw [show s2 = z0' * t0' from rfl, k328r6g_mul_smul_fix z0' t0' hz0_e1 ht0_e1, hωω2,
          one_smul]
      have hs2_e3 : s2 • (Pi.single 3 (1 : F) : Fin 4 → F) = Pi.single 3 1 := by
        rw [show s2 = z0' * t0' from rfl, k328r6g_mul_smul_fix z0' t0' hz0_e3 ht0_e3, one_mul,
          one_smul]
      have hs3_e2 : s3 • (Pi.single 2 (1 : F) : Fin 4 → F) = Pi.single 2 1 := by
        rw [show s3 = t0' from rfl, ht0_e2, one_smul]
      have hs3_e3 : s3 • (Pi.single 3 (1 : F) : Fin 4 → F) = Pi.single 3 1 := by
        rw [show s3 = t0' from rfl, ht0_e3, one_smul]
      have hcase_i : ∀ a, herm σ a a = 0 → a ≠ 0 →
          (∃ k : Fin 4, k ≠ 3 ∧ (∀ i : Fin 4, i ≠ k → i ≠ 3 → a i = 0)) → a ∈ S := by
        rintro a ha hne ⟨k, hk3, hsupp⟩
        refine ⟨hne, ha, ?_⟩
        intro ha' c hc
        fin_cases k
        ·
          have hfix : s1 • a = a := by
            have hdecomp : a = a 0 • (Pi.single 0 (1 : F) : Fin 4 → F) + a 3 • Pi.single 3 1 := by
              ext i
              fin_cases i
              · simp
              · simp [hsupp 1 (by decide) (by decide)]
              · simp [hsupp 2 (by decide) (by decide)]
              · simp
            rw [hdecomp, smul_add, smul_comm s1 (a 0) (Pi.single 0 1),
              smul_comm s1 (a 3) (Pi.single 3 1), hs1_e0, hs1_e3]
          have hcomm := k328r6g_tv_comm_of_fix hσ ha' hc s1 hfix
          have hcomm_gl : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) * (z₀ * t₀ ^ 2) =
              (z₀ * t₀ ^ 2) * ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) := by
            have h : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) * ((s1 : SUid σ 4) : GL (Fin 4) F) =
                ((s1 : SUid σ 4) : GL (Fin 4) F) * ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) :=
              congrArg (fun x : SUid σ 4 => (x : GL (Fin 4) F)) hcomm
            rwa [show ((s1 : SUid σ 4) : GL (Fin 4) F) = z₀ * t₀ ^ 2 from rfl] at h
          have hmem_c : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) ∈
              Subgroup.centralizer ({z₀ * t₀ ^ 2} : Set (GL (Fin 4) F)) := by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact hcomm_gl.symm
          have hmem_suid : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) ∈ SUid σ 4 :=
            (tv hσ ha' hc).2
          exact Subgroup.mem_sup_right ⟨hmem_suid, hmem_c⟩
        ·
          have hfix : s2 • a = a := by
            have hdecomp : a = a 1 • (Pi.single 1 (1 : F) : Fin 4 → F) + a 3 • Pi.single 3 1 := by
              ext i
              fin_cases i
              · simp [hsupp 0 (by decide) (by decide)]
              · simp
              · simp [hsupp 2 (by decide) (by decide)]
              · simp
            rw [hdecomp, smul_add, smul_comm s2 (a 1) (Pi.single 1 1),
              smul_comm s2 (a 3) (Pi.single 3 1), hs2_e1, hs2_e3]
          have hcomm := k328r6g_tv_comm_of_fix hσ ha' hc s2 hfix
          have hcomm_gl : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) * (z₀ * t₀) =
              (z₀ * t₀) * ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) := by
            have h : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) * ((s2 : SUid σ 4) : GL (Fin 4) F) =
                ((s2 : SUid σ 4) : GL (Fin 4) F) * ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) :=
              congrArg (fun x : SUid σ 4 => (x : GL (Fin 4) F)) hcomm
            rwa [show ((s2 : SUid σ 4) : GL (Fin 4) F) = z₀ * t₀ from rfl] at h
          have hmem_c : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) ∈
              Subgroup.centralizer ({z₀ * t₀} : Set (GL (Fin 4) F)) := by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact hcomm_gl.symm
          have hmem_suid : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) ∈ SUid σ 4 :=
            (tv hσ ha' hc).2
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨hmem_suid, hmem_c⟩)
        ·
          have hfix : s3 • a = a := by
            have hdecomp : a = a 2 • (Pi.single 2 (1 : F) : Fin 4 → F) + a 3 • Pi.single 3 1 := by
              ext i
              fin_cases i
              · simp [hsupp 0 (by decide) (by decide)]
              · simp [hsupp 1 (by decide) (by decide)]
              · simp
              · simp
            rw [hdecomp, smul_add, smul_comm s3 (a 2) (Pi.single 2 1),
              smul_comm s3 (a 3) (Pi.single 3 1), hs3_e2, hs3_e3]
          have hcomm := k328r6g_tv_comm_of_fix hσ ha' hc s3 hfix
          have hcomm_gl : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) * t₀ =
              t₀ * ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) := by
            have h : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) * ((s3 : SUid σ 4) : GL (Fin 4) F) =
                ((s3 : SUid σ 4) : GL (Fin 4) F) * ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) :=
              congrArg (fun x : SUid σ 4 => (x : GL (Fin 4) F)) hcomm
            rwa [show ((s3 : SUid σ 4) : GL (Fin 4) F) = t₀ from rfl] at h
          have hmem_c : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) ∈
              Subgroup.centralizer ({t₀} : Set (GL (Fin 4) F)) := by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff] at hy
            subst hy
            exact hcomm_gl.symm
          have hmem_suid : ((tv hσ ha' hc : SUid σ 4) : GL (Fin 4) F) ∈ SUid σ 4 :=
            (tv hσ ha' hc).2
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨hmem_suid, hmem_c⟩))
        · exact absurd rfl hk3
      have hcase_ii : ∀ a, herm σ a a = 0 → a ≠ 0 → a 3 ≠ 0 → a ∈ S := by
        intro a ha _ h3
        obtain ⟨hs0, hs1⟩ := exists_norm_ne_one hF' (by norm_num : (2 : ℕ) ^ 3 ≠ 2)
        let lam : F := a 3
        have hlam : lam ≠ 0 := h3
        let w : Fin 4 → F := a - lam • (Pi.single 3 (1 : F) : Fin 4 → F)
        have hw3 : w 3 = 0 := by simp [w, lam]
        have hw_decomp : a = w + lam • (Pi.single 3 (1 : F) : Fin 4 → F) := by
          simp [w, lam]
        have hw_e3 : herm σ w (Pi.single 3 (1 : F) : Fin 4 → F) = 0 := by
          rw [herm_single_right, hw3, map_zero, zero_mul]
        have he3_w : herm σ (Pi.single 3 (1 : F) : Fin 4 → F) w = 0 := by
          rw [herm_single_left, hw3, mul_zero]
        have he3_e3 : herm σ (Pi.single 3 (1 : F) : Fin 4 → F)
            (Pi.single 3 (1 : F) : Fin 4 → F) = 1 := by
          rw [herm_single_right, Pi.single_eq_same, map_one, one_mul]
        have h_expand : herm σ w w + σ lam * lam = 0 := by
          have h := ha
          rw [hw_decomp] at h
          simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
            hw_e3, he3_w, he3_e3, mul_zero, mul_one, add_zero] at h
          rw [zero_add, mul_comm lam (σ lam)] at h
          exact h
        have hww : herm σ w w = σ lam * lam := by
          have h1 : herm σ w w = - (σ lam * lam) := eq_neg_of_add_eq_zero_left h_expand
          rwa [CharTwo.neg_eq] at h1
        have hww_ne : herm σ w w ≠ 0 := by
          rw [hww]
          exact mul_ne_zero (fun h => hlam ((map_eq_zero_iff σ σ.injective).mp h)) hlam
        let u : Fin 3 → F := fun i => w (Fin.castSucc i)
        have hw_u : w = k328r6g_headEmb u := by
          ext i; fin_cases i <;> simp [u, k328r6g_headEmb, hw3]
        have hu_eq : herm σ u u = σ lam * lam := by
          have h := hww
          rw [hw_u, k328r6g_headEmb_isometry σ u u] at h
          exact h
        let u' : Fin 3 → F := lam⁻¹ • u
        have hu' : herm σ u' u' = 1 := by
          dsimp only [u']
          rw [herm_smul_left, herm_smul_right, hu_eq, map_inv₀]
          field_simp
          exact div_self (fun h => hlam ((map_eq_zero_iff σ σ.injective).mp h))
        obtain ⟨g₀, hg₀T, hg₀u⟩ := exists_mem_T_smul_eq_of_norm_one hσinv
          (Or.inr ⟨le_rfl, hs0, hs1⟩) hu'
          (show herm σ (Pi.single 0 (1 : F) : Fin 3 → F)
            (Pi.single 0 (1 : F) : Fin 3 → F) = 1 from herm_e0_e0)
        have hg0u : g₀ • u = lam • (Pi.single 0 (1 : F) : Fin 3 → F) := by
          have h := hg₀u
          dsimp only [u'] at h
          rw [smul_comm g₀ lam⁻¹ u] at h
          have h2 := congrArg (fun v => lam • v) h
          have h3 : lam • (lam⁻¹ • (g₀ • u)) = g₀ • u := by
            calc lam • (lam⁻¹ • (g₀ • u))
                = (lam * lam⁻¹) • (g₀ • u) := smul_smul lam lam⁻¹ (g₀ • u)
              _ = (1 : F) • (g₀ • u) := by rw [mul_inv_cancel₀ hlam]
              _ = g₀ • u := one_smul _ _
          rw [h3] at h2
          exact h2
        obtain ⟨g', hg'T, hg'φ, hg'orth⟩ := transport hσ (k328r6g_headEmbLinear F)
          (k328r6g_headEmb_isometry σ) hg₀T
        have hg'e3 : g' • (Pi.single 3 (1 : F) : Fin 4 → F) = Pi.single 3 1 := by
          apply hg'orth
          intro u
          simp [herm_single_right, k328r6g_headEmb_apply_three]
        have hg'W : ∀ j : Fin 3,
            (g' • k328r6g_headEmb (Pi.single j (1 : F))) 3 = 0 := by
          intro j
          have h := congrFun (hg'φ (Pi.single j (1 : F))) 3
          change (g' • k328r6g_headEmb (Pi.single j (1 : F))) 3 =
            (k328r6g_headEmb (g₀ • Pi.single j (1 : F))) 3 at h
          rw [k328r6g_headEmb_apply_three] at h
          exact h
        have hg'comm : (g' : GL (Fin 4) F) * z₀ = z₀ * g' :=
          k328r6g_comm_z0_of_head hz g' hg'e3 hg'W
        have hg'c : (g' : GL (Fin 4) F) ∈
            SUid σ 4 ⊓ Subgroup.centralizer ({z₀} : Set (GL (Fin 4) F)) := by
          refine ⟨g'.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hg'comm.symm
        have hg'J : (g' : GL (Fin 4) F) ∈ J :=
          Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hg'c))
        have hg'a : g' • a = lam • ((Pi.single 0 (1 : F) : Fin 4 → F) + Pi.single 3 1) := by
          rw [hw_decomp, smul_add, smul_comm g' lam (Pi.single 3 1), hg'e3]
          have h1 : g' • w = k328r6g_headEmb (g₀ • u) := by
            rw [hw_u]
            exact hg'φ u
          rw [h1, hg0u]
          ext k; fin_cases k <;> simp [k328r6g_headEmb]
        have hsum_iso : herm σ ((Pi.single 0 (1 : F) : Fin 4 → F) + Pi.single 3 1)
            ((Pi.single 0 (1 : F) : Fin 4 → F) + Pi.single 3 1) = 0 := by
          have h00 : herm σ (Pi.single 0 (1 : F) : Fin 4 → F)
              (Pi.single 0 (1 : F) : Fin 4 → F) = 1 := by
            rw [herm_single_right, Pi.single_eq_same, map_one, one_mul]
          have h33 : herm σ (Pi.single 3 (1 : F) : Fin 4 → F)
              (Pi.single 3 (1 : F) : Fin 4 → F) = 1 := he3_e3
          have h03 : herm σ (Pi.single 0 (1 : F) : Fin 4 → F)
              (Pi.single 3 (1 : F) : Fin 4 → F) = 0 := by
            simp [herm_single_right]
          have h30 : herm σ (Pi.single 3 (1 : F) : Fin 4 → F)
              (Pi.single 0 (1 : F) : Fin 4 → F) = 0 := by
            simp [herm_single_right]
          rw [herm_add_left, herm_add_right, herm_add_right, h00, h03, h30, h33]
          have h2 : (1 : F) + 1 = 0 := by
            have : (2 : F) = 0 := CharP.cast_eq_zero F 2
            rw [← two_mul, this, zero_mul]
          simpa using h2
        have hlam_iso : herm σ (lam • ((Pi.single 0 (1 : F) : Fin 4 → F) + Pi.single 3 1))
            (lam • ((Pi.single 0 (1 : F) : Fin 4 → F) + Pi.single 3 1)) = 0 := by
          rw [herm_smul_left, herm_smul_right, hsum_iso, mul_zero, mul_zero]
        have hlam_ne : lam • ((Pi.single 0 (1 : F) : Fin 4 → F) + Pi.single 3 1) ≠ 0 := by
          intro h
          have h0 := congrFun h 0
          simp [Pi.smul_apply, hlam] at h0
        have hlam_plane : ∃ k : Fin 4, k ≠ 3 ∧
            (∀ i : Fin 4, i ≠ k → i ≠ 3 →
              ((lam • ((Pi.single 0 (1 : F) : Fin 4 → F) + Pi.single 3 1)) : Fin 4 → F) i = 0) := by
          refine ⟨0, by decide, ?_⟩
          intro i hi hi3
          fin_cases i
          · exact absurd rfl hi
          · simp [Pi.smul_apply]
          · simp [Pi.smul_apply]
          · exact absurd rfl hi3
        have hlamS : lam • ((Pi.single 0 (1 : F) : Fin 4 → F) + Pi.single 3 1) ∈ S :=
          hcase_i _ hlam_iso hlam_ne hlam_plane
        have ha_eq : g'⁻¹ • (lam • ((Pi.single 0 (1 : F) : Fin 4 → F) + Pi.single 3 1)) = a := by
          rw [← hg'a, inv_smul_smul]
        rw [← ha_eq]
        exact hS_stable _ hlamS g'⁻¹ (J.inv_mem hg'J)
      have hcase_iii : ∀ a, herm σ a a = 0 → a ≠ 0 → a 3 = 0 → a ∈ S := by
        intro a ha hne h3
        let u : Fin 3 → F := fun i => a (Fin.castSucc i)
        have ha_u : a = k328r6g_headEmb u := by
          ext j; fin_cases j <;> simp [u, k328r6g_headEmb, h3]
        have h_exists : ∃ i : Fin 3, u i ≠ 0 := by
          by_contra! h
          apply hne
          rw [ha_u]
          ext j; fin_cases j <;> simp [k328r6g_headEmb, h]
        obtain ⟨i, hi⟩ := h_exists
        let b : Fin 4 → F := k328r6g_headEmb (Pi.single i (1 : F)) + Pi.single 3 (1 : F)
        have hb_eq : b = (Pi.single (Fin.castSucc i) (1 : F) : Fin 4 → F) + Pi.single 3 1 := by
          rw [show b = k328r6g_headEmb (Pi.single i (1 : F)) + Pi.single 3 1 from rfl,
            k328r6g_headEmb_single]
        have hsub : (Pi.single (Fin.castSucc i) (1 : F) : Fin 4 → F) 3 = 0 := by
          rw [Pi.single_apply, if_neg (Ne.symm (k328r6g_castSucc_ne_three i))]
        have hsub' : (Pi.single 3 (1 : F) : Fin 4 → F) (Fin.castSucc i) = 0 := by
          rw [Pi.single_apply, if_neg (k328r6g_castSucc_ne_three i)]
        have hb3 : b 3 = 1 := by
          rw [hb_eq, Pi.add_apply, hsub, Pi.single_eq_same, zero_add]
        have hb_ne : b ≠ 0 := by
          intro h
          have h0 := congrFun h 3
          rw [hb3, Pi.zero_apply] at h0
          exact one_ne_zero h0
        have hb_iso : herm σ b b = 0 := by
          rw [hb_eq]
          have hii : herm σ (Pi.single (Fin.castSucc i) (1 : F) : Fin 4 → F)
              (Pi.single (Fin.castSucc i) (1 : F) : Fin 4 → F) = 1 := by
            rw [herm_single_right, Pi.single_eq_same, map_one, one_mul]
          have hi3 : herm σ (Pi.single (Fin.castSucc i) (1 : F) : Fin 4 → F)
              (Pi.single 3 (1 : F) : Fin 4 → F) = 0 := by
            simp [herm_single_right, hsub]
          have h3i : herm σ (Pi.single 3 (1 : F) : Fin 4 → F)
              (Pi.single (Fin.castSucc i) (1 : F) : Fin 4 → F) = 0 := by
            simp [herm_single_left, hsub]
          have h33 : herm σ (Pi.single 3 (1 : F) : Fin 4 → F)
              (Pi.single 3 (1 : F) : Fin 4 → F) = 1 := by
            rw [herm_single_right, Pi.single_eq_same, map_one, one_mul]
          rw [herm_add_left, herm_add_right, herm_add_right, hii, hi3, h3i, h33]
          have h2 : (1 : F) + 1 = 0 := by
            have : (2 : F) = 0 := CharP.cast_eq_zero F 2
            rw [← two_mul, this, zero_mul]
          simp [h2]
        have hb_plane : ∃ k : Fin 4, k ≠ 3 ∧ (∀ l : Fin 4, l ≠ k → l ≠ 3 → b l = 0) := by
          refine ⟨Fin.castSucc i, k328r6g_castSucc_ne_three i, ?_⟩
          intro l hl hl3
          rw [hb_eq, Pi.add_apply, Pi.single_apply, Pi.single_apply, if_neg hl, if_neg hl3,
            add_zero]
        have hbS : b ∈ S := hcase_i b hb_iso hb_ne hb_plane
        obtain ⟨c₀, hc₀_ne, hc₀_trace⟩ := hσinv.exists_traceZero
        have hb_a : herm σ b a = u i := by
          rw [ha_u, hb_eq, herm_add_left, herm_single_left, herm_single_left]
          fin_cases i <;> simp [k328r6g_headEmb]
        have htv_e3 : ((tv hσ hb_iso hc₀_trace) • a) 3 ≠ 0 := by
          rw [tv_smul, hb_a, Pi.add_apply, h3, zero_add, Pi.smul_apply, smul_eq_mul, hb3, mul_one]
          exact mul_ne_zero hc₀_ne hi
        have htv_iso : herm σ ((tv hσ hb_iso hc₀_trace) • a)
            ((tv hσ hb_iso hc₀_trace) • a) = 0 := by
          rw [herm_smul_smul, ha]
        have htv_ne : (tv hσ hb_iso hc₀_trace) • a ≠ 0 := by
          intro h
          exact htv_e3 (by rw [h]; rfl)
        have htvS : (tv hσ hb_iso hc₀_trace) • a ∈ S :=
          hcase_ii _ htv_iso htv_ne htv_e3
        have htvJ : ((tv hσ hb_iso hc₀_trace : SUid σ 4) : GL (Fin 4) F) ∈ J :=
          hbS.2.2 hb_iso c₀ hc₀_trace
        have ha_eq : (tv hσ hb_iso hc₀_trace)⁻¹ • ((tv hσ hb_iso hc₀_trace) • a) = a := by
          rw [inv_smul_smul]
        rw [← ha_eq]
        exact hS_stable _ htvS (tv hσ hb_iso hc₀_trace)⁻¹ (J.inv_mem htvJ)

      intro a ha hne ha' c hc
      by_cases h3 : a 3 = 0
      · exact (hcase_iii a ha hne h3).2.2 ha' c hc
      · exact (hcase_ii a ha hne h3).2.2 ha' c hc
    have hmem : ∀ (a : Fin 4 → F) (ha : herm σ a a = 0) (c : F) (hc : c + σ c = 0),
        ((tv hσ ha hc : SUid σ 4) : GL (Fin 4) F) ∈ J := by
      intro a ha c hc
      by_cases h0 : a = 0
      · subst h0
        have h1 : tv hσ ha hc = 1 := by
          apply ext_smul
          intro v
          rw [tv_smul, one_smul]
          simp
        rw [h1]
        exact J.one_mem
      · exact hS_of_ne a ha h0 ha c hc
    have hT : (T σ 4).map (Subgroup.subtype (SUid σ 4)) ≤ J := by
      rw [Subgroup.map_le_iff_le_comap, show T σ 4 = Subgroup.closure (tvSet σ 4) from rfl,
        Subgroup.closure_le]
      rintro g ⟨a, c, ha, hc, hg⟩
      have hg' : g = tv hσ ha hc := by
        apply ext_smul
        intro v
        rw [hg, tv_smul]
      rw [hg']
      exact hmem a ha c hc
    have htop : SUid σ 4 ≤ (T σ 4).map (Subgroup.subtype (SUid σ 4)) := by
      rw [show T σ 4 = ⊤ from T_eq_top hσinv (by norm_num) (by intro h; norm_num at h)]
      intro x hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    exact le_trans htop hT

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
