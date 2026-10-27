module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactURoot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private lemma spUFix_add_add_self {F : Type} [Field F] [CharP F 2] (a b : F) :
    a + (b + a) = b := by
  rw [← add_assoc, add_comm a b, add_assoc, CharTwo.add_self_eq_zero, add_zero]

lemma spUFix_suTv_mul_apply {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}
    {e w v : Fin m → F} (hσ : IsUnitaryInvolution σ)
    (he : herm σ e e = 0) (hw : herm σ w w = 0) {d : F} (hd : d + σ d = 0)
    (h1 : (1 : F) + σ 1 = 0) :
    (suTv hσ e 1 * suTv hσ w d) • v =
      v + (d * herm σ w v) • w +
        (herm σ e v + d * herm σ e w * herm σ w v) • e := by
  rw [mul_smul, suTv_smul hσ hw hd, suTv_smul hσ he h1]
  simp only [herm_add_right, herm_smul_right, one_mul]
  module

lemma spUFix_suTv_mul_herm_e {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}
    {e w v : Fin m → F} (hσ : IsUnitaryInvolution σ)
    (he : herm σ e e = 0) (hw : herm σ w w = 0) {d : F} (hd : d + σ d = 0)
    (h1 : (1 : F) + σ 1 = 0) :
    herm σ e ((suTv hσ e 1 * suTv hσ w d) • v) =
      herm σ e v + d * herm σ e w * herm σ w v := by
  rw [spUFix_suTv_mul_apply hσ he hw hd h1]
  simp only [herm_add_right, herm_smul_right, he, mul_zero, add_zero]
  ring

lemma spUFix_suTv_mul_herm_w {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}
    {e w v : Fin m → F} (hσ : IsUnitaryInvolution σ)
    (he : herm σ e e = 0) (hw : herm σ w w = 0) {d : F} (hd : d + σ d = 0)
    (h1 : (1 : F) + σ 1 = 0)
    (hLd : d * herm σ e w * σ (herm σ e w) = 1) :
    herm σ w ((suTv hσ e 1 * suTv hσ w d) • v) =
      σ (herm σ e w) * herm σ e v := by
  rw [spUFix_suTv_mul_apply hσ he hw hd h1]
  have hwe : herm σ w e = σ (herm σ e w) := herm_conj σ hσ.invol e w
  have hcoef : (d * herm σ e w * herm σ w v) * σ (herm σ e w) = herm σ w v := by
    have h : d * herm σ e w * herm σ w v * σ (herm σ e w) =
        (d * herm σ e w * σ (herm σ e w)) * herm σ w v := by ring
    rw [h, hLd, one_mul]
  simp only [herm_add_right, herm_smul_right, hw, mul_zero, add_zero, hwe]
  rw [add_mul, hcoef]
  rw [spUFix_add_add_self (herm σ w v) (herm σ e v * σ (herm σ e w))]
  exact mul_comm _ _

lemma spUFix_suTv_mul_pow_three {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}
    {e w : Fin m → F} (hσ : IsUnitaryInvolution σ)
    (he : herm σ e e = 0) (hw : herm σ w w = 0) {d : F} (hd : d + σ d = 0)
    (h1 : (1 : F) + σ 1 = 0)
    (hLd : d * herm σ e w * σ (herm σ e w) = 1) :
    (suTv hσ e 1 * suTv hσ w d) ^ 3 = 1 := by
  set z : ↥(SUid σ m) := suTv hσ e 1 * suTv hσ w d with hz
  have step : ∀ u : Fin m → F, z • u = u + (d * herm σ w u) • w +
      (herm σ e u + d * herm σ e w * herm σ w u) • e := by
    intro u
    rw [hz]
    exact spUFix_suTv_mul_apply hσ he hw hd h1
  have hPe : ∀ u : Fin m → F,
      herm σ e (z • u) = herm σ e u + d * herm σ e w * herm σ w u := by
    intro u
    rw [hz]
    exact spUFix_suTv_mul_herm_e hσ he hw hd h1
  have hPw : ∀ u : Fin m → F,
      herm σ w (z • u) = σ (herm σ e w) * herm σ e u := by
    intro u
    rw [hz]
    exact spUFix_suTv_mul_herm_w hσ he hw hd h1 hLd
  apply ext_smul
  intro v
  rw [one_smul]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, mul_smul, mul_smul]
  have hcoef1 : d * herm σ e w * (σ (herm σ e w) * herm σ e v) = herm σ e v := by
    have h : d * herm σ e w * (σ (herm σ e w) * herm σ e v) =
        (d * herm σ e w * σ (herm σ e w)) * herm σ e v := by ring
    rw [h, hLd, one_mul]
  have hz1 : z • v = v + (d * herm σ w v) • w +
      (herm σ e v + d * herm σ e w * herm σ w v) • e := step v
  have hz2 : z • (z • v) = (z • v) + (d * (σ (herm σ e w) * herm σ e v)) • w +
      (d * herm σ e w * herm σ w v) • e := by
    rw [step (z • v), hPe v, hPw v, hcoef1]
    have hc : (herm σ e v + d * herm σ e w * herm σ w v) + herm σ e v =
        d * herm σ e w * herm σ w v := by
      rw [add_comm (herm σ e v) (d * herm σ e w * herm σ w v), add_assoc,
        CharTwo.add_self_eq_zero, add_zero]
    rw [hc]
  rw [step (z • (z • v)), hPe (z • v), hPw (z • v), hPe v, hPw v, hz2, hz1]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  match_scalars
  · rfl
  · linear_combination (d * herm σ w v) * hLd
        + (d * herm σ w v + d * (σ (herm σ e w) * herm σ e v)) * h2
  · linear_combination (2 * herm σ e v + d * herm σ e w * herm σ w v) * hLd
        + (2 * herm σ e v + 2 * (d * herm σ e w * herm σ w v)) * h2

theorem exists_mul_pow_three_spUFixRootU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {e w : Fin m → F} (he : herm (unitaryInvolution F 2 n) e e = 0)
    (hw : herm (unitaryInvolution F 2 n) w w = 0)
    (hew : herm (unitaryInvolution F 2 n) e w ≠ 0) :
    ∃ x ∈ spUFixRootU hF m e, ∃ y ∈ spUFixRootU hF m w, (x * y) ^ 3 = 1 ∧ x * y ≠ 1 := by
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 n) :=
    isUnitaryInvolution_unitaryInvolution hF
  have h1 : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]; exact CharTwo.add_self_eq_zero 1
  set d : F := (herm (unitaryInvolution F 2 n) e w *
      unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w))⁻¹ with hddef
  have hL0 : herm (unitaryInvolution F 2 n) e w ≠ 0 := hew
  have hS0 : unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w) ≠ 0 :=
    fun h => hL0 ((unitaryInvolution F 2 n).injective (by rw [h, map_zero]))
  have hLd : d * herm (unitaryInvolution F 2 n) e w *
      unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w) = 1 := by
    rw [hddef]
    rw [show (herm (unitaryInvolution F 2 n) e w *
        unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w))⁻¹ *
        herm (unitaryInvolution F 2 n) e w *
        unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w) =
        (herm (unitaryInvolution F 2 n) e w *
        unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w))⁻¹ *
        (herm (unitaryInvolution F 2 n) e w *
        unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w)) from by ring]
    exact inv_mul_cancel₀ (mul_ne_zero hL0 hS0)
  have hsd : unitaryInvolution F 2 n d = d := by
    rw [hddef, map_inv₀, map_mul, hσ.invol]
    congr 1
    exact mul_comm _ _
  have hd : d + unitaryInvolution F 2 n d = 0 := by
    rw [hsd, CharTwo.add_self_eq_zero]
  set z : ↥(SUid (unitaryInvolution F 2 n) m) :=
    suTv hσ e 1 * suTv hσ w d with hz
  have hxy : kFactsSuProjTv hF m e 1 * kFactsSuProjTv hF m w d =
      kFactsSuProj hF m z := by
    rw [hz]
    unfold kFactsSuProjTv
    rw [← map_mul]
  have hcube : (kFactsSuProjTv hF m e 1 * kFactsSuProjTv hF m w d) ^ 3 = 1 := by
    rw [hxy, ← map_pow]
    rw [show z ^ 3 = 1 from by
      rw [hz]; exact spUFix_suTv_mul_pow_three hσ he hw hd h1 hLd]
    rw [map_one]
  have hne : kFactsSuProjTv hF m e 1 * kFactsSuProjTv hF m w d ≠ 1 := by
    intro h
    have hproj : kFactsSuProj hF m z =
        kFactsSuProj hF m (1 : ↥(SUid (unitaryInvolution F 2 n) m)) := by
      rw [← hxy, h, map_one]
    obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hF z
      (1 : ↥(SUid (unitaryInvolution F 2 n) m))).mp hproj
    have hu1 : (1 : Matrix (Fin m) (Fin m) F) =
        (((z : ↥(SUid (unitaryInvolution F 2 n) m)) : GL (Fin m) F) :
          Matrix (Fin m) (Fin m) F) *
          ((u : F) • (1 : Matrix (Fin m) (Fin m) F)) := by
      simpa using hu
    have hzmat : (((z : ↥(SUid (unitaryInvolution F 2 n) m)) : GL (Fin m) F) :
        Matrix (Fin m) (Fin m) F) =
        ((u : F)⁻¹) • (1 : Matrix (Fin m) (Fin m) F) := by
      have huz : (1 : Matrix (Fin m) (Fin m) F) =
          (u : F) • (((z : ↥(SUid (unitaryInvolution F 2 n) m)) : GL (Fin m) F) :
            Matrix (Fin m) (Fin m) F) := by
        rw [hu1, Matrix.mul_smul, Matrix.mul_one]
      rw [huz, smul_smul, inv_mul_cancel₀ (Units.ne_zero u), one_smul]
    have hze : z • e =
        (d * unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w)) • w := by
      rw [hz]
      rw [spUFix_suTv_mul_apply hσ he hw hd h1]
      have hwe : herm (unitaryInvolution F 2 n) w e =
          unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w) :=
        herm_conj (unitaryInvolution F 2 n) hσ.invol e w
      rw [he, hwe, zero_add, hLd, one_smul]
      have h2e : e + e = 0 := by
        have h : e + e = ((1 : F) + 1) • e := by rw [add_smul, one_smul]
        rw [h, CharTwo.add_self_eq_zero (1 : F), zero_smul]
      rw [add_comm e ((d * unitaryInvolution F 2 n
          (herm (unitaryInvolution F 2 n) e w)) • w), add_assoc, h2e, add_zero]
    have hze' : z • e = ((u : F)⁻¹) • e := by
      rw [smul_def, hzmat, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hee : ((u : F)⁻¹) • e =
        (d * unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w)) • w :=
      hze'.symm.trans hze
    have hew' : e = ((u : F) * d *
        unitaryInvolution F 2 n (herm (unitaryInvolution F 2 n) e w)) • w := by
      calc e = (u : F) • ((u : F)⁻¹ • e) := by
            rw [smul_smul, mul_inv_cancel₀ (Units.ne_zero u), one_smul]
        _ = (u : F) • ((d * unitaryInvolution F 2 n
              (herm (unitaryInvolution F 2 n) e w)) • w) := by rw [hee]
        _ = ((u : F) * d * unitaryInvolution F 2 n
              (herm (unitaryInvolution F 2 n) e w)) • w := by
            rw [smul_smul, ← mul_assoc]
    have hzero : herm (unitaryInvolution F 2 n) e w = 0 := by
      rw [hew', herm_smul_left, hw, mul_zero]
    exact hew hzero
  exact ⟨kFactsSuProjTv hF m e 1, Subgroup.subset_closure ⟨1, h1, rfl⟩,
    kFactsSuProjTv hF m w d, Subgroup.subset_closure ⟨d, hd, rfl⟩, hcube, hne⟩

end CFSG.LocalAnalysis.WeakClosure81

end
