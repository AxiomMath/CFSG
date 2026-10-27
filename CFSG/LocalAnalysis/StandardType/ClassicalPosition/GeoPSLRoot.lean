module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LinearAlgebra.RootGroupSL.SLTransitive

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType
open Matrix


private abbrev gSLr_V (m : ℕ) (F : Type) := Fin (m + 1) → F

private def gSLr_root (m : ℕ) (i j : Fin (m + 1)) : Fin m → ℤ := fun k =>
  (if i.val ≤ k.val then 1 else 0) - (if j.val ≤ k.val then 1 else 0)

private theorem gSLr_toStd_root (m : ℕ) (i j : Fin (m + 1)) :
    SpecialLinear.toStd m (gSLr_root m i j) = Pi.single i 1 - Pi.single j 1 := by
  funext a
  have ha := a.isLt
  have hi := i.isLt
  have hj := j.isLt
  simp only [SpecialLinear.toStd, gSLr_root, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem gSLr_root_mem_roots (m : ℕ) (F : Type) [Field F]
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    gSLr_root m i j ∈ (SpecialLinear.rootDatum m F).roots := by
  show gSLr_root m i j ∈ roots (SpecialLinear.isFiniteType_A m) ∅
  rw [SpecialLinear.roots_eq]
  exact ⟨i, j, hij, gSLr_toStd_root m i j⟩

private theorem gSLr_exists_longRoot (m : ℕ) (F : Type) [Field F] (hm : 1 ≤ m) :
    ∃ β : Fin m → ℤ, β ∈ (SpecialLinear.rootDatum m F).roots ∧
      GGLongRoot (SpecialLinear.rootDatum m F) β ∧
      SpecialLinear.toStd m β = Pi.single 0 1 - Pi.single (Fin.last m) 1 := by
  have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  let β : Fin m → ℤ := gSLr_root m 0 (Fin.last m)
  have hβ : β ∈ (SpecialLinear.rootDatum m F).roots := gSLr_root_mem_roots m F h0last
  have hstd : SpecialLinear.toStd m β =
      Pi.single 0 1 - Pi.single (Fin.last m) 1 := gSLr_toStd_root m 0 (Fin.last m)
  have hmax : ∀ δ ∈ (SpecialLinear.rootDatum m F).roots, ∑ i, δ i ≤ ∑ i, β i := by
    intro δ hδ
    have hδ' : δ ∈ roots (SpecialLinear.isFiniteType_A m) ∅ := hδ
    rw [SpecialLinear.roots_eq] at hδ'
    obtain ⟨i, j, hij, hδij⟩ := hδ'
    have h1 : ∑ k, δ k = (j : ℤ) - i := SpecialLinear.ht_eq m hδij
    have h2 : ∑ k, β k = (Fin.last m : ℤ) - 0 := SpecialLinear.ht_eq m hstd
    rw [h1, h2]
    have hj : (j : ℤ) ≤ (m : ℤ) := by
      have h : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
      exact_mod_cast h
    have hi : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg _
    have hlm : (Fin.last m : ℤ) = (m : ℤ) := by simp
    rw [hlm]
    omega
  refine ⟨β, hβ, ?_, hstd⟩
  refine ⟨1, β, hβ, hmax, ?_⟩
  rw [map_one]
  exact (Module.End.one_apply β).symm

private def gSLr_dual {m : ℕ} {F : Type} [Field F] (φ : Fin (m + 1) → F) :
    gSLr_V m F →ₗ[F] F where
  toFun := fun x => φ ⬝ᵥ x
  map_add' := by intro x y; rw [dotProduct_add]
  map_smul' := by intro a x; simp [dotProduct_smul]

private theorem gSLr_dual_apply {m : ℕ} {F : Type} [Field F] (φ : Fin (m + 1) → F)
    (x : gSLr_V m F) : gSLr_dual φ x = φ ⬝ᵥ x := rfl

private theorem gSLr_e0_ne {m : ℕ} {F : Type} [Field F] (hm : 1 ≤ m) :
    (Pi.single (0 : Fin (m + 1)) 1 : gSLr_V m F) ≠ 0 := by
  have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  intro h
  have := congrArg (fun x => x 0) h
  simpa using this

private theorem gSLr_v_ne {m : ℕ} {F : Type} [Field F] {v φ' : gSLr_V m F}
    (h4 : φ' ⬝ᵥ v = 1) : v ≠ 0 := by
  intro hv
  rw [hv, dotProduct_zero] at h4
  exact one_ne_zero h4.symm

private theorem gSLr_dual_ne {m : ℕ} {F : Type} [Field F] {φ v : gSLr_V m F}
    (h : φ ⬝ᵥ v = 1) : gSLr_dual φ ≠ 0 := by
  intro h0
  have := congrArg (fun f => f v) h0
  simp [gSLr_dual] at this
  rw [this] at h
  exact one_ne_zero h.symm

private theorem gSLr_elastDual_e0 {m : ℕ} {F : Type} [Field F] (hm : 1 ≤ m) :
    (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F)
      (Pi.single (0 : Fin (m + 1)) 1) = 0 := by
  have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  simp [Pi.single_eq_of_ne (Ne.symm h0last)]

private theorem gSLr_e0Dual_elast {m : ℕ} {F : Type} [Field F] (hm : 1 ≤ m) :
    (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F)
      (Pi.single (Fin.last m) 1) = 0 := by
  have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  simp [Pi.single_eq_of_ne h0last]

private theorem gSLr_elastDual_elast {m : ℕ} {F : Type} [Field F] :
    (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F)
      (Pi.single (Fin.last m) 1) = 1 := by
  simp

private theorem gSLr_e0Dual_e0 {m : ℕ} {F : Type} [Field F] :
    (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F)
      (Pi.single (0 : Fin (m + 1)) 1) = 1 := by
  simp


private theorem gSLr_elastDual_ne (m : ℕ) (F : Type) [Field F] :
    (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) ≠ 0 := by
  intro h
  have := congrArg (fun f => f (Pi.single (Fin.last m) 1 : gSLr_V m F)) h
  simp at this

private theorem gSLr_exists_lin (m : ℕ) (F : Type) [Field F] (hm2 : 2 ≤ m)
    (v φ v' φ' : gSLr_V m F) (h1 : φ ⬝ᵥ v = 0) (h2 : φ' ⬝ᵥ v' = 0) (h3 : φ ⬝ᵥ v' = 1)
    (h4 : φ' ⬝ᵥ v = 1) :
    ∃ u : SpecialLinearGroup F (gSLr_V m F),
      u (Pi.single (0 : Fin (m + 1)) 1) = v ∧
      u (Pi.single (Fin.last m) 1) = v' ∧
      (∀ x, gSLr_dual φ (u x) =
        (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) x) ∧
      (∀ x, gSLr_dual φ' (u x) =
        (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F) x) := by
  have hm : 1 ≤ m := by omega
  have hV : 3 ≤ Module.finrank F (gSLr_V m F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  obtain ⟨g, hg1, hg2⟩ := CFSG.LinearAlgebra.RootGroupSL.exists_specialLinear_apply_eq_of_incident
    (E := F) (V := gSLr_V m F) hV
    (w := Pi.single (0 : Fin (m + 1)) 1) (w' := v)
    (l := LinearMap.proj (Fin.last m)) (l' := gSLr_dual φ)
    (gSLr_e0_ne hm) (gSLr_v_ne h4) (gSLr_elastDual_ne m F) (gSLr_dual_ne h3)
    (gSLr_elastDual_e0 hm) h1
  let w : gSLr_V m F := (g : gSLr_V m F ≃ₗ[F] gSLr_V m F).symm v'
  have hgw : g w = v' := LinearEquiv.apply_symm_apply _ _
  have hw : (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) w = 1 := by
    have h := hg2 w
    rw [hgw, gSLr_dual_apply, h3] at h
    exact h.symm
  have hzero1 : (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F)
      (w - Pi.single (Fin.last m) 1) = 0 := by
    rw [map_sub, hw, gSLr_elastDual_elast, sub_self]
  let k1 : SpecialLinearGroup F (gSLr_V m F) :=
    ⟨LinearEquiv.transvection hzero1, LinearEquiv.transvection.det_eq_one hzero1⟩
  have k1_e0 : k1 (Pi.single (0 : Fin (m + 1)) 1) = Pi.single (0 : Fin (m + 1)) 1 := by
    change (LinearEquiv.transvection hzero1) (Pi.single (0 : Fin (m + 1)) 1) =
      Pi.single (0 : Fin (m + 1)) 1
    rw [LinearEquiv.transvection.apply, gSLr_elastDual_e0 hm, zero_smul, add_zero]
  have k1_elast : k1 (Pi.single (Fin.last m) 1) = w := by
    change (LinearEquiv.transvection hzero1) (Pi.single (Fin.last m) 1) = w
    rw [LinearEquiv.transvection.apply, gSLr_elastDual_elast, one_smul]
    abel
  have k1_form : ∀ x, (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) (k1 x) =
      (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) x := by
    intro x
    change (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F)
      ((LinearEquiv.transvection hzero1) x) = _
    rw [LinearEquiv.transvection.apply, map_add, map_smul, hzero1, smul_zero, add_zero]
  let ψ : gSLr_V m F →ₗ[F] F := (gSLr_dual φ').comp (g : gSLr_V m F →ₗ[F] gSLr_V m F)
  let ψ' : gSLr_V m F →ₗ[F] F := ψ.comp (k1 : gSLr_V m F →ₗ[F] gSLr_V m F)
  have hpsi_e0 : ψ (Pi.single (0 : Fin (m + 1)) 1) = 1 := by
    change gSLr_dual φ' (g (Pi.single (0 : Fin (m + 1)) 1)) = 1
    rw [hg1, gSLr_dual_apply, h4]
  have hpsi'_e0 : ψ' (Pi.single (0 : Fin (m + 1)) 1) = 1 := by
    change ψ (k1 (Pi.single (0 : Fin (m + 1)) 1)) = 1
    rw [k1_e0, hpsi_e0]
  have hzero2 : (ψ' - (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F))
      (-(Pi.single (0 : Fin (m + 1)) 1)) = 0 := by
    rw [map_neg, LinearMap.sub_apply, hpsi'_e0, gSLr_e0Dual_e0, sub_self, neg_zero]
  let k2 : SpecialLinearGroup F (gSLr_V m F) :=
    ⟨LinearEquiv.transvection hzero2, LinearEquiv.transvection.det_eq_one hzero2⟩
  have k2_e0 : k2 (Pi.single (0 : Fin (m + 1)) 1) = Pi.single (0 : Fin (m + 1)) 1 := by
    change (LinearEquiv.transvection hzero2) (Pi.single (0 : Fin (m + 1)) 1) =
      Pi.single (0 : Fin (m + 1)) 1
    rw [LinearEquiv.transvection.apply]
    have h : (ψ' - (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F))
        (Pi.single (0 : Fin (m + 1)) 1) = 0 := by
      rw [LinearMap.sub_apply, hpsi'_e0, gSLr_e0Dual_e0, sub_self]
    rw [h, zero_smul, add_zero]
  have k2_elast : k2 (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 := by
    change (LinearEquiv.transvection hzero2) (Pi.single (Fin.last m) 1) =
      Pi.single (Fin.last m) 1
    rw [LinearEquiv.transvection.apply]
    have h : (ψ' - (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F))
        (Pi.single (Fin.last m) 1) = 0 := by
      rw [LinearMap.sub_apply]
      have hh : ψ' (Pi.single (Fin.last m) 1) = 0 := by
        change ψ (k1 (Pi.single (Fin.last m) 1)) = 0
        rw [k1_elast]
        change gSLr_dual φ' (g w) = 0
        rw [hgw, gSLr_dual_apply, h2]
      rw [hh, gSLr_e0Dual_elast hm, sub_zero]
    rw [h, zero_smul, add_zero]
  have k2_form : ∀ x, ψ' (k2 x) = (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F) x := by
    intro x
    change ψ' ((LinearEquiv.transvection hzero2) x) = _
    rw [LinearEquiv.transvection.apply, map_add, map_smul]
    have hneg : ψ' (-(Pi.single (0 : Fin (m + 1)) 1)) = -1 := by
      rw [map_neg, hpsi'_e0]
    rw [hneg, smul_eq_mul, LinearMap.sub_apply]
    ring
  have k2_elastDual : ∀ x,
      (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) (k2 x) =
      (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) x := by
    intro x
    change (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F)
      ((LinearEquiv.transvection hzero2) x) = _
    rw [LinearEquiv.transvection.apply, map_add, map_smul, map_neg, gSLr_elastDual_e0 hm,
      neg_zero, smul_zero, add_zero]
  let k : SpecialLinearGroup F (gSLr_V m F) := k1 * k2
  have k_e0 : k (Pi.single (0 : Fin (m + 1)) 1) = Pi.single (0 : Fin (m + 1)) 1 := by
    change k1 (k2 (Pi.single (0 : Fin (m + 1)) 1)) = _
    rw [k2_e0, k1_e0]
  have k_elast : k (Pi.single (Fin.last m) 1) = w := by
    change k1 (k2 (Pi.single (Fin.last m) 1)) = w
    rw [k2_elast, k1_elast]
  have k_form : ∀ x, (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) (k x) =
      (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) x := by
    intro x
    change (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) (k1 (k2 x)) = _
    rw [k1_form, k2_elastDual]
  have k_psi : ∀ x, ψ (k x) = (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F) x := by
    intro x
    change ψ (k1 (k2 x)) = _
    change ψ' (k2 x) = _
    rw [k2_form]
  refine ⟨g * k, ?_, ?_, ?_, ?_⟩
  · change g (k (Pi.single (0 : Fin (m + 1)) 1)) = v
    rw [k_e0, hg1]
  · change g (k (Pi.single (Fin.last m) 1)) = v'
    rw [k_elast, hgw]
  · intro x
    change gSLr_dual φ (g (k x)) = _
    rw [hg2, k_form]
  · intro x
    change gSLr_dual φ' (g (k x)) = _
    change ψ (k x) = _
    rw [k_psi]


private theorem gSLr_transvection_coe {m : ℕ} {F : Type} [Field F]
    {i j : Fin (m + 1)} (hij : i ≠ j) (b : F) :
    ((Matrix.SpecialLinearGroup.transvection hij b :
      Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      1 + b • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe,
    show Matrix.single i j b = b • Matrix.single i j 1 by
      rw [smul_single, smul_eq_mul, mul_one],
    Matrix.single_eq_single_vecMulVec_single]

private theorem gSLr_toLin_matrix_apply (m : ℕ) (F : Type) [Field F]
    (um : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (u : SpecialLinearGroup F (gSLr_V m F))
    (hum : (Matrix.SpecialLinearGroup.toLin_equiv (Pi.basisFun F (Fin (m + 1)))) um = u)
    (z : gSLr_V m F) :
    (um : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ z = u z := by
  have h := Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq
    (Pi.basisFun F (Fin (m + 1))) um
  rw [hum] at h
  have h2 := LinearMap.congr_fun h.symm z
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply] at h2
  simpa using h2

private theorem gSLr_matrix_props (m : ℕ) (F : Type) [Field F]
    (v φ v' φ' : gSLr_V m F)
    (u : SpecialLinearGroup F (gSLr_V m F))
    (hu0 : u (Pi.single (0 : Fin (m + 1)) 1) = v)
    (hul : u (Pi.single (Fin.last m) 1) = v')
    (huφ : ∀ x, gSLr_dual φ (u x) =
      (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) x)
    (huφ' : ∀ x, gSLr_dual φ' (u x) =
      (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F) x) :
    ∃ um : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      (um : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
          Pi.single (0 : Fin (m + 1)) 1 = v ∧
      (um : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
          Pi.single (Fin.last m) 1 = v' ∧
      Pi.single (Fin.last m) 1 ᵥ*
        ((um⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) = φ ∧
      Pi.single (0 : Fin (m + 1)) 1 ᵥ*
        ((um⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) = φ' := by
  let b := Pi.basisFun F (Fin (m + 1))
  let um : Matrix.SpecialLinearGroup (Fin (m + 1)) F :=
    (Matrix.SpecialLinearGroup.toLin_equiv b).symm u
  have hum : (Matrix.SpecialLinearGroup.toLin_equiv b) um = u :=
    (Matrix.SpecialLinearGroup.toLin_equiv b).apply_symm_apply u
  have hu_inv : (Matrix.SpecialLinearGroup.toLin_equiv b) um⁻¹ = u⁻¹ := by
    rw [← hum, map_inv]
  have hmat : ∀ z, (um : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ z = u z :=
    gSLr_toLin_matrix_apply m F um u hum
  have hmat_inv : ∀ z, ((um⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ z = u⁻¹ z :=
    gSLr_toLin_matrix_apply m F um⁻¹ u⁻¹ hu_inv
  have hm0 : (um : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
      Pi.single (0 : Fin (m + 1)) 1 = v := by rw [hmat, hu0]
  have hml : (um : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ
      Pi.single (Fin.last m) 1 = v' := by rw [hmat, hul]
  have hdotl : ∀ z, (Pi.single (Fin.last m) 1 ᵥ*
      ((um⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F)) ⬝ᵥ z = φ ⬝ᵥ z := by
    intro z
    rw [← dotProduct_mulVec, hmat_inv]
    have h1 : (Pi.single (Fin.last m) 1 : gSLr_V m F) ⬝ᵥ (u⁻¹ z) =
        (LinearMap.proj (Fin.last m) : gSLr_V m F →ₗ[F] F) (u⁻¹ z) := by
      simp [dotProduct_comm, dotProduct_single, LinearMap.proj]
    rw [h1, ← huφ (u⁻¹ z)]
    have h2 : u (u⁻¹ z) = z := LinearEquiv.apply_symm_apply _ _
    rw [h2, gSLr_dual_apply]
  have hrowl : Pi.single (Fin.last m) 1 ᵥ*
      ((um⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = φ := by
    funext i
    have h := hdotl (Pi.single i 1)
    simpa using h
  have hdotr : ∀ z, (Pi.single (0 : Fin (m + 1)) 1 ᵥ*
      ((um⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F)) ⬝ᵥ z = φ' ⬝ᵥ z := by
    intro z
    rw [← dotProduct_mulVec, hmat_inv]
    have h1 : (Pi.single (0 : Fin (m + 1)) 1 : gSLr_V m F) ⬝ᵥ (u⁻¹ z) =
        (LinearMap.proj (0 : Fin (m + 1)) : gSLr_V m F →ₗ[F] F) (u⁻¹ z) := by
      simp [dotProduct_comm, dotProduct_single, LinearMap.proj]
    rw [h1, ← huφ' (u⁻¹ z)]
    have h2 : u (u⁻¹ z) = z := LinearEquiv.apply_symm_apply _ _
    rw [h2, gSLr_dual_apply]
  have hrowr : Pi.single (0 : Fin (m + 1)) 1 ᵥ*
      ((um⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = φ' := by
    funext i
    have h := hdotr (Pi.single i 1)
    simpa using h
  exact ⟨um, hm0, hml, hrowl, hrowr⟩


private theorem gSLr_conj_vecMulVec (m : ℕ) (F : Type) [Field F]
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (x y x' y' : gSLr_V m F) (c : F)
    (hx : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *ᵥ x = x')
    (hy : y ᵥ* ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) = y') :
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (1 + c • Matrix.vecMulVec x y) *
        ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      1 + c • Matrix.vecMulVec x' y' := by
  have hwu : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hwu, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hx, hy]

private theorem gSLr_map_conj (m : ℕ) (F : Type) [Field F]
    {i j : Fin (m + 1)} (hij : i ≠ j)
    {β : Fin m → ℤ} (hroot : SpecialLinear.toStd m β = Pi.single i 1 - Pi.single j 1)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hconj : ∀ c : F, (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (1 + c • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)) *
        ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + c • M) :
    (((SpecialLinear.rootGroup m F β).map (MulAut.conj u).toMonoidHom).map
        Matrix.SpecialLinearGroup.toGL) =
      Subgroup.closure {g : GL (Fin (m + 1)) F | ∃ c : F,
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + c • M} := by
  rw [SpecialLinear.rootGroup_eq m F hij hroot]
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    change x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u))
      (SpecialLinear.rootSubgroup m F hij) at hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [SpecialLinear.mem_rootSubgroup] at hy
    obtain ⟨c, rfl⟩ := hy
    refine Subgroup.subset_closure ⟨c, ?_⟩
    have hcoe : ((Matrix.SpecialLinearGroup.toGL
        ((MulAut.conj u) (Matrix.SpecialLinearGroup.transvection hij c)) :
          GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          (1 + c • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)) *
          ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
      rw [MulAut.conj_apply, map_mul, map_mul]
      change (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          ((Matrix.SpecialLinearGroup.transvection hij c :
            Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
          ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F) = _
      rw [gSLr_transvection_coe hij c]
    exact hcoe.trans (hconj c)
  · rw [Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    change g ∈ Subgroup.map Matrix.SpecialLinearGroup.toGL
      (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u)) (SpecialLinear.rootSubgroup m F hij))
    rw [Subgroup.mem_map]
    refine ⟨(MulAut.conj u) (Matrix.SpecialLinearGroup.transvection hij c), ?_, ?_⟩
    · change (MulAut.conj u) (Matrix.SpecialLinearGroup.transvection hij c) ∈
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u)) (SpecialLinear.rootSubgroup m F hij)
      rw [Subgroup.mem_map]
      exact ⟨Matrix.SpecialLinearGroup.transvection hij c,
        SpecialLinear.transvection_mem_rootSubgroup hij c, rfl⟩
    · apply Units.ext
      have hcoe : ((Matrix.SpecialLinearGroup.toGL
          ((MulAut.conj u) (Matrix.SpecialLinearGroup.transvection hij c)) :
            GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
            (1 + c • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1)) *
            ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
        rw [MulAut.conj_apply, map_mul, map_mul]
        change (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
            ((Matrix.SpecialLinearGroup.transvection hij c :
              Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
            ((u⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) F) = _
        rw [gSLr_transvection_coe hij c]
      rw [hcoe, hconj c]
      exact hc.symm

private theorem gSLr_main_ge2 (m : ℕ) (F : Type) [Field F] (hm2 : 2 ≤ m)
    (v φ v' φ' : gSLr_V m F) (h1 : φ ⬝ᵥ v = 0) (h2 : φ' ⬝ᵥ v' = 0) (h3 : φ ⬝ᵥ v' = 1)
    (h4 : φ' ⬝ᵥ v = 1) :
    ∃ β, β ∈ (SpecialLinear.rootDatum m F).roots ∧
      GGLongRoot (SpecialLinear.rootDatum m F) β ∧
      ∃ u : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
        (((SpecialLinear.rootDatum m F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v φ ∧
          (((SpecialLinear.rootDatum m F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v' φ' := by
  have hm : 1 ≤ m := by omega
  have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  obtain ⟨β, hβ, hlong, hstd⟩ := gSLr_exists_longRoot m F hm
  obtain ⟨u_lin, hu0, hul, huφ, huφ'⟩ := gSLr_exists_lin m F hm2 v φ v' φ' h1 h2 h3 h4
  obtain ⟨u, hum0, huml, hum_rowl, hum_rowr⟩ :=
    gSLr_matrix_props m F v φ v' φ' u_lin hu0 hul huφ huφ'
  have hstd_neg : SpecialLinear.toStd m (-β) =
      Pi.single (Fin.last m) 1 - Pi.single 0 1 := by
    rw [SpecialLinear.toStd_neg, hstd]
    abel
  refine ⟨β, hβ, hlong, u, ?_, ?_⟩
  · change (((SpecialLinear.rootGroup m F β).map (MulAut.conj u).toMonoidHom).map
        Matrix.SpecialLinearGroup.toGL) = matTransvGroup v φ
    rw [gSLr_map_conj m F h0last hstd u (Matrix.vecMulVec v φ)
      (fun c => gSLr_conj_vecMulVec m F u (Pi.single (0 : Fin (m + 1)) 1)
        (Pi.single (Fin.last m) 1) v φ c hum0 hum_rowl)]
    rfl
  · change (((SpecialLinear.rootGroup m F (-β)).map (MulAut.conj u).toMonoidHom).map
        Matrix.SpecialLinearGroup.toGL) = matTransvGroup v' φ'
    rw [gSLr_map_conj m F h0last.symm hstd_neg u (Matrix.vecMulVec v' φ')
      (fun c => gSLr_conj_vecMulVec m F u (Pi.single (Fin.last m) 1)
        (Pi.single (0 : Fin (m + 1)) 1) v' φ' c huml hum_rowr)]
    rfl


private theorem gSLr_matTransvGroup_smul_left (m : ℕ) (F : Type) [Field F]
    (a : F) (ha : a ≠ 0) (v φ : gSLr_V m F) :
    matTransvGroup (a • v) φ = matTransvGroup v φ := by
  unfold matTransvGroup
  congr 1
  ext g
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c * a, ?_⟩
    rw [hc, Matrix.smul_vecMulVec, smul_smul]
  · rintro ⟨c, hc⟩
    refine ⟨c * a⁻¹, ?_⟩
    rw [hc, Matrix.smul_vecMulVec, smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]

private theorem gSLr_matTransvGroup_smul_right (m : ℕ) (F : Type) [Field F]
    (a : F) (ha : a ≠ 0) (v φ : gSLr_V m F) :
    matTransvGroup v (a • φ) = matTransvGroup v φ := by
  unfold matTransvGroup
  congr 1
  ext g
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c * a, ?_⟩
    rw [hc, Matrix.vecMulVec_smul, smul_smul]
  · rintro ⟨c, hc⟩
    refine ⟨c * a⁻¹, ?_⟩
    rw [hc, Matrix.vecMulVec_smul, smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]

private theorem gSLr_main_eq_one (F : Type) [Field F]
    (v φ v' φ' : Fin 2 → F) (h1 : φ ⬝ᵥ v = 0) (h2 : φ' ⬝ᵥ v' = 0) (h3 : φ ⬝ᵥ v' = 1)
    (h4 : φ' ⬝ᵥ v = 1) :
    ∃ β, β ∈ (SpecialLinear.rootDatum 1 F).roots ∧
      GGLongRoot (SpecialLinear.rootDatum 1 F) β ∧
      ∃ u : Matrix.SpecialLinearGroup (Fin 2) F,
        (((SpecialLinear.rootDatum 1 F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v φ ∧
          (((SpecialLinear.rootDatum 1 F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v' φ' := by
  have h0last : (0 : Fin 2) ≠ 1 := by decide
  have hv : v ≠ 0 := gSLr_v_ne h4
  have hli : LinearIndependent F ![v, v'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hφ : s * (φ ⬝ᵥ v) + t * (φ ⬝ᵥ v') = 0 := by
      have := congrArg (fun x => φ ⬝ᵥ x) hst
      simpa [dotProduct_add, dotProduct_smul, smul_eq_mul] using this
    have hφ' : s * (φ' ⬝ᵥ v) + t * (φ' ⬝ᵥ v') = 0 := by
      have := congrArg (fun x => φ' ⬝ᵥ x) hst
      simpa [dotProduct_add, dotProduct_smul, smul_eq_mul] using this
    rw [h1, h3] at hφ
    rw [h4, h2] at hφ'
    constructor
    · simpa using hφ'
    · simpa using hφ
  let u₀ : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i j => if j = 0 then v i else v' i
  have hcol0 : u₀.col 0 = v := by
    funext i
    simp [u₀, Matrix.col_apply]
  have hcol1 : u₀.col 1 = v' := by
    funext i
    simp [u₀, Matrix.col_apply, h0last]
  have hcol_eq : u₀.col = ![v, v'] := by
    funext j
    fin_cases j
    · simpa using hcol0
    · simpa using hcol1
  have hcols : LinearIndependent F u₀.col := by
    rw [hcol_eq]; exact hli
  have hun : IsUnit u₀.det := (Matrix.isUnit_iff_isUnit_det u₀).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcols)
  have hdet : u₀.det ≠ 0 := hun.ne_zero
  let d : F := u₀.det
  let D : Matrix (Fin 2) (Fin 2) F :=
    Matrix.diagonal fun j : Fin 2 => if j = 0 then d⁻¹ else 1
  let u_mat : Matrix (Fin 2) (Fin 2) F := u₀ * D
  have hDdet : D.det = d⁻¹ := by
    rw [Matrix.det_diagonal]
    rw [Finset.prod_eq_single (0 : Fin 2)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hd1 : u_mat.det = 1 := by
    rw [show u_mat = u₀ * D from rfl, Matrix.det_mul, hDdet]
    exact mul_inv_cancel₀ hdet
  let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨u_mat, hd1⟩
  have hum0 : u_mat *ᵥ (Pi.single (0 : Fin 2) 1) = d⁻¹ • v := by
    rw [show u_mat = u₀ * D from rfl, ← Matrix.mulVec_mulVec]
    have hDe0 : D *ᵥ (Pi.single (0 : Fin 2) 1) = d⁻¹ • Pi.single (0 : Fin 2) 1 := by
      ext i
      simp [D, Matrix.mulVec, Matrix.diagonal, Pi.single_apply, h0last]
      by_cases hi : i = 0 <;> simp [hi]
    rw [hDe0, Matrix.mulVec_smul, Matrix.mulVec_single_one, hcol0]
  have hum1 : u_mat *ᵥ (Pi.single (1 : Fin 2) 1) = v' := by
    rw [show u_mat = u₀ * D from rfl, ← Matrix.mulVec_mulVec]
    have hDe1 : D *ᵥ (Pi.single (1 : Fin 2) 1) = Pi.single (1 : Fin 2) 1 := by
      ext i
      simp [D, Matrix.mulVec, Matrix.diagonal, Pi.single_apply, h0last]
      by_cases hi : i = 1 <;> simp [hi]
    rw [hDe1, Matrix.mulVec_single_one, hcol1]
  have hrowl0 : φ ᵥ* u₀ = Pi.single (1 : Fin 2) 1 := by
    funext j
    fin_cases j
    · simpa [Matrix.vecMul, dotProduct, u₀, Matrix.col_apply] using h1
    · simpa [Matrix.vecMul, dotProduct, u₀, Matrix.col_apply] using h3
  have hrowr0 : φ' ᵥ* u₀ = Pi.single (0 : Fin 2) 1 := by
    funext j
    fin_cases j
    · simpa [Matrix.vecMul, dotProduct, u₀, Matrix.col_apply] using h4
    · simpa [Matrix.vecMul, dotProduct, u₀, Matrix.col_apply] using h2
  have hrowl : φ ᵥ* (u₀ * D) = Pi.single (1 : Fin 2) 1 := by
    rw [← Matrix.vecMul_vecMul, hrowl0]
    ext j
    fin_cases j <;> simp [D, Matrix.vecMul, Matrix.diagonal, h0last]
  have hrowr : φ' ᵥ* (u₀ * D) = d⁻¹ • Pi.single (0 : Fin 2) 1 := by
    rw [← Matrix.vecMul_vecMul, hrowr0]
    ext j
    fin_cases j <;> simp [D, Matrix.vecMul, Matrix.diagonal, h0last]
  have hwu : u_mat * ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = 1 := by
    change (u : Matrix (Fin 2) (Fin 2) F) *
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hwu' : ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) * u_mat = 1 := by
    change ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (u : Matrix (Fin 2) (Fin 2) F) = 1
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hmatinv : u_mat⁻¹ = ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) := Matrix.inv_eq_left_inv hwu'
  have hmatmul : u_mat * u_mat⁻¹ = 1 := by rw [hmatinv, hwu]
  have hrowl' : Pi.single (1 : Fin 2) 1 ᵥ*
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = φ := by
    rw [← hmatinv]
    have h : (φ ᵥ* u_mat) ᵥ* u_mat⁻¹ = φ := by
      rw [Matrix.vecMul_vecMul, hmatmul, Matrix.vecMul_one]
    rwa [hrowl] at h
  have hrowr' : Pi.single (0 : Fin 2) 1 ᵥ*
      ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = d • φ' := by
    rw [← hmatinv]
    have h : (φ' ᵥ* u_mat) ᵥ* u_mat⁻¹ = φ' := by
      rw [Matrix.vecMul_vecMul, hmatmul, Matrix.vecMul_one]
    rw [hrowr] at h
    have h2 : d⁻¹ • ((Pi.single (0 : Fin 2) 1) ᵥ* u_mat⁻¹) = φ' := by
      simpa [Matrix.smul_vecMul] using h
    have h3 : d • (d⁻¹ • ((Pi.single (0 : Fin 2) 1) ᵥ* u_mat⁻¹)) = d • φ' := by rw [h2]
    rwa [smul_smul, mul_inv_cancel₀ hdet, one_smul] at h3
  obtain ⟨β, hβ, hlong, hstd⟩ := gSLr_exists_longRoot 1 F le_rfl
  have hstd_neg : SpecialLinear.toStd 1 (-β) =
      Pi.single (Fin.last 1) 1 - Pi.single 0 1 := by
    rw [SpecialLinear.toStd_neg, hstd]
    abel
  refine ⟨β, hβ, hlong, u, ?_, ?_⟩
  · change (((SpecialLinear.rootGroup 1 F β).map (MulAut.conj u).toMonoidHom).map
        Matrix.SpecialLinearGroup.toGL) = matTransvGroup v φ
    rw [gSLr_map_conj 1 F (show (0 : Fin 2) ≠ Fin.last 1 by decide) hstd u
      (Matrix.vecMulVec (d⁻¹ • v) φ)
      (fun c => gSLr_conj_vecMulVec 1 F u (Pi.single (0 : Fin 2) 1)
        (Pi.single (Fin.last 1) 1) (d⁻¹ • v) φ c hum0 hrowl')]
    exact gSLr_matTransvGroup_smul_left 1 F d⁻¹ (inv_ne_zero hdet) v φ
  · change (((SpecialLinear.rootGroup 1 F (-β)).map (MulAut.conj u).toMonoidHom).map
        Matrix.SpecialLinearGroup.toGL) = matTransvGroup v' φ'
    rw [gSLr_map_conj 1 F (show (Fin.last 1) ≠ (0 : Fin 2) by decide) hstd_neg u
      (Matrix.vecMulVec v' (d • φ'))
      (fun c => gSLr_conj_vecMulVec 1 F u (Pi.single (Fin.last 1) 1)
        (Pi.single (0 : Fin 2) 1) v' (d • φ') c hum1 hrowr')]
    exact gSLr_matTransvGroup_smul_right 1 F d hdet v' φ'

private theorem gSLr_main_all (m : ℕ) (F : Type) [Field F] (hm : 1 ≤ m)
    (v φ v' φ' : gSLr_V m F) (h1 : φ ⬝ᵥ v = 0) (h2 : φ' ⬝ᵥ v' = 0) (h3 : φ ⬝ᵥ v' = 1)
    (h4 : φ' ⬝ᵥ v = 1) :
    ∃ β, β ∈ (SpecialLinear.rootDatum m F).roots ∧
      GGLongRoot (SpecialLinear.rootDatum m F) β ∧
      ∃ u : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
        (((SpecialLinear.rootDatum m F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v φ ∧
          (((SpecialLinear.rootDatum m F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v' φ' := by
  rcases Nat.eq_or_lt_of_le hm with rfl | hm2
  · exact gSLr_main_eq_one F v φ v' φ' h1 h2 h3 h4
  · exact gSLr_main_ge2 m F (by omega) v φ v' φ' h1 h2 h3 h4



theorem exists_conj_rootGroup_eq_matTransvGroup_PSL (m : ℕ) (F : Type) [Field F] (hm : 1 ≤ m)
    (v φ v' φ' : Fin (m + 1) → F) (h1 : φ ⬝ᵥ v = 0) (h2 : φ' ⬝ᵥ v' = 0) (h3 : φ ⬝ᵥ v' = 1)
    (h4 : φ' ⬝ᵥ v = 1) :
    ∃ β, β ∈ (SpecialLinear.rootDatum m F).roots ∧ GGLongRoot (SpecialLinear.rootDatum m F) β ∧
      ∃ u : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
        (((SpecialLinear.rootDatum m F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v φ ∧
          (((SpecialLinear.rootDatum m F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
            Matrix.SpecialLinearGroup.toGL = matTransvGroup v' φ' := by
  exact gSLr_main_all m F hm v φ v' φ' h1 h2 h3 h4

end CFSG.StandardType.ClassicalPosition
