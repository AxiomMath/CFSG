module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommAux
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosLiftE
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRank
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommCornerGrp
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux9

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

@[expose] noncomputable def ggNSPosPF3C_scalarGL {K : Type} [Field K] {n : ℕ} (z : K) (hz0 : z ≠ 0) :
    GL (Fin n) K :=
  Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 z hz0)

theorem ggNSPosPF3C_scalar_pow_three {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hp : p = 3) {b₁ b₂ : G} (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs)
    {g₁ g₂ : GL (Fin n) K} (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) {z : K}
    (hz : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = z • 1) :
    z ^ 3 = 1 := by
  have h3 := ggNSPosPF_commutator_pow_prime_aux h hb₁ hb₂ h₁ h₂ hz
  rwa [hp] at h3

private theorem ggNSPosPF3C_smul_one_pow {K : Type} [Semiring K] {n : ℕ} (z : K) (k : ℕ) :
    (z • (1 : Matrix (Fin n) (Fin n) K)) ^ k = z ^ k • 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, Matrix.smul_mul, Matrix.one_mul, smul_smul, pow_succ]

theorem ggNSPosPF3C_scalarGL_coe {K : Type} [Field K] {n : ℕ} (z : K) (hz0 : z ≠ 0) :
    ((ggNSPosPF3C_scalarGL (n := n) z hz0 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = z • 1 := by
  unfold ggNSPosPF3C_scalarGL
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem ggNSPosPF3C_scalar_pow_card {K : Type} [Field K] {f : ℕ} {z : K} (hz3 : z ^ 3 = 1)
    (hdvd : 3 ∣ 2 ^ f + 1) : z ^ (2 ^ f + 1) = 1 := by
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul, hz3, one_pow]

theorem ggNSPosPF3C_scalar_ne_zero {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hn : n = 6) {b₁ b₂ : G} (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs)
    {g₁ g₂ : GL (Fin n) K} (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) {z : K}
    (hz : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = z • 1) :
    z ≠ 0 := by
  intro h0
  have h := ggNSPosPF_commutator_pow_n_aux h hb₁ hb₂ h₁ h₂ hz
  rw [h0, hn] at h
  norm_num at h

theorem ggNSPosPF3C_scalarGL_pow_three {K : Type} [Field K] {n : ℕ} {z : K} (hz0 : z ≠ 0)
    (hz3 : z ^ 3 = 1) : ggNSPosPF3C_scalarGL (n := n) z hz0 ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ggNSPosPF3C_scalarGL_coe, ggNSPosPF3C_smul_one_pow, hz3, one_smul,
    Units.val_one]

theorem ggNSPosPF3C_scalarGL_eq_one_iff {K : Type} [Field K] {n : ℕ} (hn : 0 < n) {z : K}
    (hz0 : z ≠ 0) : ggNSPosPF3C_scalarGL (n := n) z hz0 = 1 ↔ z = 1 := by
  constructor
  · intro h
    have h00 := congrArg (fun g : GL (Fin n) K => ((g : Matrix (Fin n) (Fin n) K)) ⟨0, hn⟩ ⟨0, hn⟩) h
    rw [ggNSPosPF3C_scalarGL_coe] at h00
    simpa using h00
  · intro h
    subst h
    apply Units.ext
    rw [ggNSPosPF3C_scalarGL_coe, Units.val_one]
    simp

theorem ggNSPosPF3C_scalarGL_mem_SUid {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {z : K}
    (hz3 : z ^ 3 = 1) (hzn : z ^ n = 1) (hz0 : z ≠ 0) (hdvd : 3 ∣ 2 ^ f + 1) :
    ggNSPosPF3C_scalarGL (n := n) z hz0 ∈ SUid (unitaryInvolution K 2 f) n := by
  rw [mem_SUid]
  refine ⟨?_, ?_⟩
  · rw [ggNSPosPF3C_scalarGL_coe, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact hzn
  · rw [ggNSPosPF3C_scalarGL_coe]
    have hmap : conjTr (unitaryInvolution K 2 f) (z • (1 : Matrix (Fin n) (Fin n) K)) =
        (unitaryInvolution K 2 f z) • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
        Matrix.one_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    have hσ : unitaryInvolution K 2 f z * z = 1 := by
      rw [unitaryInvolution_apply, ← pow_succ]
      exact ggNSPosPF3C_scalar_pow_card hz3 hdvd
    rw [hmap, Matrix.smul_mul, Matrix.one_mul, smul_smul, hσ, one_smul]

@[expose] noncomputable def ggNSPosPF3C_scalarSU {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (z : K) (hz3 : z ^ 3 = 1) (hzn : z ^ n = 1) (hz0 : z ≠ 0) (hdvd : 3 ∣ 2 ^ f + 1) :
    Su K 2 f n :=
  ⟨ggNSPosPF3C_scalarGL (n := n) z hz0,
    ggNSPosPF3C_scalarGL_mem_SUid hz3 hzn hz0 hdvd⟩

theorem ggNSPosPF3C_scalarSU_coe {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} (z : K)
    (hz3 : z ^ 3 = 1) (hzn : z ^ n = 1) (hz0 : z ≠ 0) (hdvd : 3 ∣ 2 ^ f + 1) :
    ((ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd : Su K 2 f n) : GL (Fin n) K) =
      ggNSPosPF3C_scalarGL (n := n) z hz0 := rfl

theorem ggNSPosPF3C_scalarSU_mem_centralizer {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {z : K}
    (hz3 : z ^ 3 = 1) (hzn : z ^ n = 1) (hz0 : z ≠ 0) (hdvd : 3 ∣ 2 ^ f + 1) :
    ψ (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd) ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨g, hg⟩ := h.acts b hb
  obtain ⟨y, hy_eq, hy_psi⟩ := hg.2 (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd)
  have hyx : y = ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd := by
    apply Subtype.ext
    rw [hy_eq, ggNSPosPF3C_scalarSU_coe]
    have hcomm : g * ggNSPosPF3C_scalarGL (n := n) z hz0 =
        ggNSPosPF3C_scalarGL (n := n) z hz0 * g := by
      unfold ggNSPosPF3C_scalarGL
      exact (Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 z hz0) g).symm
    calc g * ggNSPosPF3C_scalarGL (n := n) z hz0 * g⁻¹
        = ggNSPosPF3C_scalarGL (n := n) z hz0 * g * g⁻¹ := by rw [hcomm]
      _ = ggNSPosPF3C_scalarGL (n := n) z hz0 := by group
  have hthis : b * ψ (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd) * b⁻¹ =
      ψ (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd) := by
    rw [hy_psi, hyx]
  have h1 : b * ψ (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd) =
      ψ (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd) * b := by
    calc b * ψ (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd)
        = b * ψ (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd) * b⁻¹ * b := by group
      _ = ψ (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd) * b := by rw [hthis]
  exact h1

theorem ggNSPosPF3C_scalarSU_mem_Bs {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hp : p = 3) {z : K} (hz3 : z ^ 3 = 1) (hzn : z ^ n = 1)
    (hz0 : z ≠ 0) (hdvd : 3 ∣ 2 ^ f + 1) :
    ψ (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd) ∈ Bs := by
  refine h.bstar.2.2.2 _ (ggNSPosPF3C_scalarSU_mem_centralizer h hz3 hzn hz0 hdvd) ?_
  have hx3 : (ggNSPosPF3C_scalarSU z hz3 hzn hz0 hdvd) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ggNSPosPF3C_scalarSU_coe, Subgroup.coe_one]
    exact ggNSPosPF3C_scalarGL_pow_three hz0 hz3
  rw [hp, ← map_pow, hx3, map_one]


private theorem ggNSPosPF3C_induces_inv {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} {b : G} {g : GL (Fin n) K}
    (hg : GGInducesUnitary (p := 2) (f := f) ψ b g) :
    GGInducesUnitary (p := 2) (f := f) ψ b⁻¹ g⁻¹ := by
  have hzU : ggIsUnitaryMat (p := 2) (f := f) g⁻¹ := ggNSPosPA_ggIsUnitaryMat_inv hg.1
  refine ⟨hzU, fun x => ?_⟩
  let x' : Su K 2 f n := ⟨g⁻¹ * (x : GL (Fin n) K) * g, InnerDiagSU.conj_mem_SUid hzU x.2⟩
  obtain ⟨y, hy, hby⟩ := hg.2 x'
  have hyx : y = x := by
    apply Subtype.ext
    rw [hy]
    change g * (g⁻¹ * (x : GL (Fin n) K) * g) * g⁻¹ = (x : GL (Fin n) K)
    group
  refine ⟨x', ?_, ?_⟩
  · change (x' : GL (Fin n) K) = g⁻¹ * (x : GL (Fin n) K) * (g⁻¹)⁻¹
    rw [inv_inv]
  · rw [hyx] at hby
    rw [show (b⁻¹)⁻¹ = b from inv_inv b]
    rw [← hby]
    group

private def ggNSPosPF3C_Lam {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (ψ : Su K 2 f 6 →* G) (Bs : Subgroup G) : Subgroup (GL (Fin 6) K) where
  carrier := {g | ∃ b ∈ Bs, GGInducesUnitary (p := 2) (f := f) ψ b g}
  mul_mem' := by
    rintro _ _ ⟨b, hb, hbg⟩ ⟨c, hc, hch⟩
    exact ⟨b * c, Bs.mul_mem hb hc, ggNSPosPA7_induces_mul hbg hch⟩
  one_mem' := by
    refine ⟨1, Bs.one_mem, ?_⟩
    have h1 := ggNSPosPA_induces_self (ψ := ψ) (1 : Su K 2 f 6)
    rwa [map_one, Subgroup.coe_one] at h1
  inv_mem' := by
    rintro _ ⟨b, hb, hbg⟩
    exact ⟨b⁻¹, Bs.inv_mem hb, ggNSPosPF3C_induces_inv hbg⟩

section Retained

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f : ℕ} {ψ : Su K 2 f 6 →* G}

private theorem ggNSPosPF3C_cube_roots {z ζ : K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hζ : ζ ^ 3 = 1) :
    ∃ k : ℕ, k < 3 ∧ ζ = z ^ k := by
  have hs : 1 + z + z ^ 2 = 0 := by
    have h1 : (z - 1) * (1 + z + z ^ 2) = 0 := by linear_combination hz3
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hz1)
  have h2 : (ζ - 1) * ((ζ - z) * (ζ - z ^ 2)) = 0 := by
    linear_combination hζ - ζ ^ 2 * hs + ζ * hs + ζ * hz3 - hz3
  rcases mul_eq_zero.mp h2 with h | h
  · exact ⟨0, by norm_num, by rw [pow_zero]; exact sub_eq_zero.mp h⟩
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨1, by norm_num, by rw [pow_one]; exact sub_eq_zero.mp h⟩
    · exact ⟨2, by norm_num, sub_eq_zero.mp h⟩

private theorem ggNSPosPF3C_x_facts (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {z : K} (hz0 : z ≠ 0)
    (hz3 : z ^ 3 = 1) {x : Su K 2 f 6}
    (hx : (x : GL (Fin 6) K) = ggNSPosPF3C_scalarGL (n := 6) z hz0) (hxne : ψ x ≠ 1) :
    orderOf (ψ x) = 3 ∧ ψ x ∈ Bs ∧ ∀ s : Su K 2 f 6, ψ x * ψ s = ψ s * ψ x := by
  have hz6 : z ^ 6 = 1 := by rw [show 6 = 3 * 2 by norm_num, pow_mul, hz3, one_pow]
  have hdvd : 3 ∣ 2 ^ f + 1 := h.dvd
  have hxS : x = ggNSPosPF3C_scalarSU z hz3 hz6 hz0 hdvd :=
    Subtype.ext (by rw [hx, ggNSPosPF3C_scalarSU_coe])
  refine ⟨?_, ?_, ?_⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ hxne
    have hx3 : x ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hx, ggNSPosPF3C_scalarGL_pow_three hz0 hz3, Subgroup.coe_one])
    rw [← map_pow, hx3, map_one]
  · rw [hxS]
    exact ggNSPosPF3C_scalarSU_mem_Bs h rfl hz3 hz6 hz0 hdvd
  · intro s
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx]
    exact Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 z hz0) (s : GL (Fin 6) K)

private theorem ggNSPosPF3C_rel (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {z : K} (hz1 : z ≠ 1) (hz0 : z ≠ 0)
    (hz3 : z ^ 3 = 1) {x : Su K 2 f 6}
    (hx : (x : GL (Fin 6) K) = ggNSPosPF3C_scalarGL (n := 6) z hz0) (hord : orderOf (ψ x) = 3)
    (hcx : ∀ s : Su K 2 f 6, ψ x * ψ s = ψ s * ψ x) {b b' : G} (hb : b ∈ Bs) (hb' : b' ∈ Bs)
    {Y : Su K 2 f 6} (hY : GGInducesUnitary (p := 2) (f := f) ψ b (Y : GL (Fin 6) K))
    {g' : GL (Fin 6) K} (hg' : GGInducesUnitary (p := 2) (f := f) ψ b' g') :
    ∃ k : ℕ, (ψ Y)⁻¹ * b' * ψ Y = (ψ x) ^ k * b' ∧
      ((ψ x) ^ k = 1 → g' * (Y : GL (Fin 6) K) = (Y : GL (Fin 6) K) * g') := by
  obtain ⟨ζ, hζ⟩ := ggNSPosPF_commutator_scalar h hb' hb hg' hY
  have hζ3 : ζ ^ 3 = 1 := ggNSPosPF3C_scalar_pow_three h rfl hb' hb hg' hY hζ
  have hζ0 : ζ ≠ 0 := ggNSPosPF3C_scalar_ne_zero h rfl hb' hb hg' hY hζ
  have hζ6 : ζ ^ 6 = 1 := by rw [show 6 = 3 * 2 by norm_num, pow_mul, hζ3, one_pow]
  have hdvd : 3 ∣ 2 ^ f + 1 := h.dvd
  have hc : ggNSPosPF_commutator g' (Y : GL (Fin 6) K) = ggNSPosPF3C_scalarGL (n := 6) ζ hζ0 :=
    Units.ext (by rw [hζ, ggNSPosPF3C_scalarGL_coe])
  have hc' : g' * (Y : GL (Fin 6) K) * g'⁻¹ * (Y : GL (Fin 6) K)⁻¹ =
      ggNSPosPF3C_scalarGL (n := 6) ζ hζ0 := hc
  have hconj : g' * (Y : GL (Fin 6) K) * g'⁻¹ =
      ggNSPosPF3C_scalarGL (n := 6) ζ hζ0 * (Y : GL (Fin 6) K) := by
    rw [← hc']
    group
  obtain ⟨y₀, hy₀, hbY⟩ := hg'.2 Y
  have hy₀Z : y₀ = ggNSPosPF3C_scalarSU ζ hζ3 hζ6 hζ0 hdvd * Y :=
    Subtype.ext (by rw [hy₀, Subgroup.coe_mul, ggNSPosPF3C_scalarSU_coe, hconj])
  obtain ⟨k, hk3, hk⟩ := ggNSPosPF3C_cube_roots hz3 hz1 hζ3
  have hZk : ggNSPosPF3C_scalarSU ζ hζ3 hζ6 hζ0 hdvd = x ^ k := by
    subst hk
    apply Subtype.ext
    rw [ggNSPosPF3C_scalarSU_coe, Subgroup.coe_pow, hx]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ggNSPosPF3C_scalarGL_coe, ggNSPosPF3C_scalarGL_coe,
      ggNSPosPF3C_smul_one_pow]
  have hrel0 : b' * ψ Y * b'⁻¹ = (ψ x) ^ k * ψ Y := by
    rw [hbY, hy₀Z, hZk, map_mul, map_pow]
  have hcom : Commute (ψ x) (ψ Y) := hcx Y
  have hcu : (ψ x) ^ k * ψ Y = ψ Y * (ψ x) ^ k := (hcom.pow_left k).eq
  refine ⟨k, ?_, fun h1 => ?_⟩
  · have h2 : b' * ψ Y = (ψ x) ^ k * ψ Y * b' := by
      rw [← mul_inv_eq_iff_eq_mul]
      exact hrel0
    calc (ψ Y)⁻¹ * b' * ψ Y = (ψ Y)⁻¹ * (b' * ψ Y) := by rw [mul_assoc]
      _ = (ψ Y)⁻¹ * ((ψ x) ^ k * ψ Y * b') := by rw [h2]
      _ = (ψ x) ^ k * b' := by rw [hcu]; group
  · have hk0 : k = 0 := by
      have h2 : orderOf (ψ x) ∣ k := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at h2
      omega
    have hζ1 : ζ = 1 := by rw [hk, hk0, pow_zero]
    have hc1 : ggNSPosPF_commutator g' (Y : GL (Fin 6) K) = 1 :=
      hc.trans ((ggNSPosPF3C_scalarGL_eq_one_iff (n := 6) (by norm_num) hζ0).mpr hζ1)
    exact (ggNSPosPF_commutator_eq_one_iff _ _).mp hc1

private theorem ggNSPosPF3C_det_one_commute (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {z : K} (hz1 : z ≠ 1)
    (hz0 : z ≠ 0) (hz3 : z ^ 3 = 1) {x : Su K 2 f 6}
    (hx : (x : GL (Fin 6) K) = ggNSPosPF3C_scalarGL (n := 6) z hz0) (hxne : ψ x ≠ 1)
    {y g' : GL (Fin 6) K} (hy : y ∈ ggNSPosPF3C_Lam ψ Bs)
    (hdet : (y : Matrix (Fin 6) (Fin 6) K).det = 1) (hg' : g' ∈ ggNSPosPF3C_Lam ψ Bs) :
    g' * y = y * g' := by
  classical
  obtain ⟨b, hb, hY⟩ := hy
  obtain ⟨hord, hψx, hcx⟩ := ggNSPosPF3C_x_facts h hz0 hz3 hx hxne
  let Y : Su K 2 f 6 := ⟨y, mem_SUid.mpr ⟨hdet, hY.1⟩⟩
  have hY' : GGInducesUnitary (p := 2) (f := f) ψ b (Y : GL (Fin 6) K) := hY
  show g' * (Y : GL (Fin 6) K) = (Y : GL (Fin 6) K) * g'
  have hE : Nat.card ↥(Subgroup.zpowers (ψ x)) = 3 := by rw [Nat.card_zpowers]; exact hord
  have hcom : Commute (ψ x) (ψ Y) := hcx Y
  have hcommBs : ∀ a ∈ Bs, ∀ c ∈ Bs, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (h.bstar.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩)
  have hrel : ∀ c ∈ Bs, ∃ k : ℕ, (ψ Y)⁻¹ * c * ψ Y = (ψ x) ^ k * c := by
    intro c hc
    obtain ⟨g'', hg''⟩ := h.acts c hc
    obtain ⟨k, hk, -⟩ := ggNSPosPF3C_rel (Y := Y) h hz1 hz0 hz3 hx hord hcx hb hc hY' hg''
    exact ⟨k, hk⟩
  have hNorm : (ψ Y)⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := by
    apply ggNSPosPF3C_mem_normalizer_of_conj_mem
    intro c hc
    obtain ⟨k, hk⟩ := hrel c hc
    rw [inv_inv, hk]
    exact Bs.mul_mem (Bs.pow_mem hψx k) hc
  have hEg : ∀ e ∈ Subgroup.zpowers (ψ x), (ψ Y)⁻¹ * e * (ψ Y)⁻¹⁻¹ = e := by
    intro e he
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have hc : Commute ((ψ x) ^ m) (ψ Y) := hcom.zpow_left m
    rw [inv_inv]
    calc (ψ Y)⁻¹ * (ψ x) ^ m * ψ Y = (ψ Y)⁻¹ * ((ψ x) ^ m * ψ Y) := mul_assoc _ _ _
      _ = (ψ Y)⁻¹ * (ψ Y * (ψ x) ^ m) := by rw [hc.eq]
      _ = (ψ x) ^ m := inv_mul_cancel_left _ _
  have hmv : ∀ c ∈ Bs, c⁻¹ * ((ψ Y)⁻¹ * c * (ψ Y)⁻¹⁻¹) ∈ Subgroup.zpowers (ψ x) := by
    intro c hc
    obtain ⟨k, hk⟩ := hrel c hc
    rw [inv_inv, hk, hcommBs _ (Bs.pow_mem hψx k) c hc, inv_mul_cancel_left]
    exact (Subgroup.zpowers (ψ x)).pow_mem (Subgroup.mem_zpowers _) k
  have hTL := ggNSPosPF3C_conj_trivial_of_noTransvection h.bstar.2.1 h.noTr hE hNorm hEg hmv
  obtain ⟨b', hb', hg'⟩ := hg'
  obtain ⟨k, hk, himp⟩ := ggNSPosPF3C_rel (Y := Y) h hz1 hz0 hz3 hx hord hcx hb hb' hY' hg'
  have h1 : (ψ x) ^ k = 1 := by
    have h2 := hTL b' hb'
    rw [inv_inv, hk] at h2
    exact mul_right_cancel (h2.trans (one_mul b').symm)
  exact himp h1

end Retained

theorem ggNSPosPF3C_retained_centre_contradiction {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {ψ : Su K 2 f 6 →* G}
    (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {b₁ b₂ : G} (hb₁ : b₁ ∈ Bs) (hb₂ : b₂ ∈ Bs) {g₁ g₂ : GL (Fin 6) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁) (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) {z : K}
    (hz : ((ggNSPosPF_commutator g₁ g₂ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = z • 1) (hz1 : z ≠ 1)
    (hz0 : z ≠ 0) {x : Su K 2 f 6} (hx : (x : GL (Fin 6) K) = ggNSPosPF3C_scalarGL (n := 6) z hz0)
    (hxne : ψ x ≠ 1) : False := by
  classical
  have hz3 : z ^ 3 = 1 := ggNSPosPF3C_scalar_pow_three h rfl hb₁ hb₂ h₁ h₂ hz
  have hg₁ : g₁ ∈ ggNSPosPF3C_Lam ψ Bs := ⟨b₁, hb₁, h₁⟩
  have hg₂ : g₂ ∈ ggNSPosPF3C_Lam ψ Bs := ⟨b₂, hb₂, h₂⟩
  let fdet : ↥(ggNSPosPF3C_Lam ψ Bs) →* Kˣ :=
    Matrix.GeneralLinearGroup.det.comp (ggNSPosPF3C_Lam ψ Bs).subtype
  have hker : fdet.ker ≤ Subgroup.center ↥(ggNSPosPF3C_Lam ψ Bs) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g'
    have hdet : ((y : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      have h1 : fdet y = 1 := MonoidHom.mem_ker.mp hy
      have h2 : Matrix.GeneralLinearGroup.det (y : GL (Fin 6) K) = 1 := h1
      have h3 := congrArg Units.val h2
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h3
    exact Subtype.ext (ggNSPosPF3C_det_one_commute h hz1 hz0 hz3 hx hxne y.2 hdet g'.2)
  have hcomm : g₁ * g₂ = g₂ * g₁ :=
    congrArg Subtype.val ((fdet.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm
      (⟨g₁, hg₁⟩ : ↥(ggNSPosPF3C_Lam ψ Bs)) ⟨g₂, hg₂⟩)
  have hc1 : ggNSPosPF_commutator g₁ g₂ = 1 := (ggNSPosPF_commutator_eq_one_iff g₁ g₂).mpr hcomm
  have hcz : ggNSPosPF_commutator g₁ g₂ = ggNSPosPF3C_scalarGL (n := 6) z hz0 :=
    Units.ext (by rw [hz, ggNSPosPF3C_scalarGL_coe])
  exact hz1 ((ggNSPosPF3C_scalarGL_eq_one_iff (n := 6) (by norm_num) hz0).mp (hcz ▸ hc1))

end CFSG.StandardType

end
