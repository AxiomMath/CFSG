module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthAlg

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p m : ℕ}

structure OrthFrame (p m : ℕ) (f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p)) where
  s : Fin m → ZMod p
  s' : Fin m → ZMod p
  a : Fin m → ZMod p
  symm : ∀ x y, f x y = f y x
  two_ne : (2 : ZMod p) ≠ 0
  isotropic_s : f s s = 0
  isotropic_s' : f s' s' = 0
  pair : f s s' = 1
  norm_a : f a a = -2
  a_orth_s : f a s = 0
  a_orth_s' : f a s' = 0

namespace OrthFrame

variable {f} (F : OrthFrame p m f)

@[expose] def U : Submodule (ZMod p) (Fin m → ZMod p) :=
  LinearMap.ker (f.flip F.s) ⊓ LinearMap.ker (f.flip F.s')

theorem mem_U {w : Fin m → ZMod p} : w ∈ F.U ↔ f w F.s = 0 ∧ f w F.s' = 0 := by
  simp [U]

theorem a_mem_U : F.a ∈ F.U := F.mem_U.2 ⟨F.a_orth_s, F.a_orth_s'⟩

@[expose] def siegelLin (w : Fin m → ZMod p) : (Fin m → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.id + (f.flip F.s).smulRight w - (f.flip w).smulRight F.s -
    ((2 : ZMod p)⁻¹ * f w w) • (f.flip F.s).smulRight F.s

theorem siegelLin_apply (w x : Fin m → ZMod p) :
    F.siegelLin w x =
      x + f x F.s • w - f x w • F.s - ((2 : ZMod p)⁻¹ * f w w * f x F.s) • F.s := by
  simp [siegelLin, smul_smul, mul_assoc]

private theorem siegelLin_f_s {w : Fin m → ZMod p} (hw : f w F.s = 0) (x : Fin m → ZMod p) :
    f (F.siegelLin w x) F.s = f x F.s := by
  rw [F.siegelLin_apply]
  simp [map_add, map_sub, map_smul, hw, F.isotropic_s]

private theorem siegelLin_f_orth {w w' : Fin m → ZMod p} (hw' : f w' F.s = 0)
    (x : Fin m → ZMod p) :
    f (F.siegelLin w x) w' = f x w' + f x F.s * f w w' := by
  have hsw' : f F.s w' = 0 := (F.symm w' F.s).symm.trans hw'
  rw [F.siegelLin_apply]
  simp [map_add, map_sub, map_smul, hsw', smul_eq_mul]

theorem siegelLin_zero : F.siegelLin 0 = 1 := by
  refine LinearMap.ext fun x => ?_
  simpa using F.siegelLin_apply 0 x

theorem siegelLin_add [Fact p.Prime] {w₁ w₂ : Fin m → ZMod p} (h₁ : f w₁ F.s = 0)
    (h₂ : f w₂ F.s = 0) : F.siegelLin (w₁ + w₂) = F.siegelLin w₁ * F.siegelLin w₂ := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply]
  rw [F.siegelLin_apply, F.siegelLin_apply (x := F.siegelLin w₂ x)]
  rw [F.siegelLin_f_s h₂ x, F.siegelLin_f_orth h₁ x]
  rw [F.siegelLin_apply]
  have hww : f (w₁ + w₂) (w₁ + w₂) = f w₁ w₁ + 2 * f w₁ w₂ + f w₂ w₂ := by
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, F.symm w₂ w₁]
    ring
  rw [hww]
  simp only [map_add, F.symm w₂ w₁]
  match_scalars
  all_goals
    first
    | field_simp [F.two_ne]
      ring
    | ring

theorem toMatrix'_siegelLin_mul_neg [Fact p.Prime] {w : Fin m → ZMod p} (hw : f w F.s = 0) :
    LinearMap.toMatrix' (F.siegelLin w) * LinearMap.toMatrix' (F.siegelLin (-w)) = 1 := by
  have hneg : f (-w) F.s = 0 := by simpa using hw
  rw [← LinearMap.toMatrix'_mul, ← F.siegelLin_add hw hneg, add_neg_cancel,
    F.siegelLin_zero, LinearMap.toMatrix'_one]

theorem toMatrix'_siegelLin_neg_mul [Fact p.Prime] {w : Fin m → ZMod p} (hw : f w F.s = 0) :
    LinearMap.toMatrix' (F.siegelLin (-w)) * LinearMap.toMatrix' (F.siegelLin w) = 1 := by
  have hneg : f (-w) F.s = 0 := by simpa using hw
  rw [← LinearMap.toMatrix'_mul, ← F.siegelLin_add hneg hw, neg_add_cancel,
    F.siegelLin_zero, LinearMap.toMatrix'_one]

@[expose] def siegel [Fact p.Prime] (w : Fin m → ZMod p) : GL (Fin m) (ZMod p) :=
  if hw : f w F.s = 0 then
    ⟨LinearMap.toMatrix' (F.siegelLin w), LinearMap.toMatrix' (F.siegelLin (-w)),
      F.toMatrix'_siegelLin_mul_neg hw, F.toMatrix'_siegelLin_neg_mul hw⟩
  else 1

variable [Fact p.Prime]

private theorem siegel_coe_toMatrix' {w : Fin m → ZMod p} (hw : f w F.s = 0) :
    (F.siegel w : Matrix (Fin m) (Fin m) (ZMod p)) = LinearMap.toMatrix' (F.siegelLin w) := by
  rw [siegel, dif_pos hw]

theorem siegel_mulVec {w : Fin m → ZMod p} (hw : f w F.s = 0) (x : Fin m → ZMod p) :
    (F.siegel w : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x =
      x + f x F.s • w - f x w • F.s - ((2 : ZMod p)⁻¹ * f w w * f x F.s) • F.s := by
  rw [F.siegel_coe_toMatrix' hw, LinearMap.toMatrix'_mulVec]
  exact F.siegelLin_apply w x

theorem siegel_zero : F.siegel 0 = 1 := by
  apply Units.ext
  rw [F.siegel_coe_toMatrix' (by simp : f 0 F.s = 0), F.siegelLin_zero,
    LinearMap.toMatrix'_one, Matrix.GeneralLinearGroup.coe_one]

theorem siegel_add {w₁ w₂ : Fin m → ZMod p} (h₁ : f w₁ F.s = 0) (h₂ : f w₂ F.s = 0) :
    F.siegel (w₁ + w₂) = F.siegel w₁ * F.siegel w₂ := by
  have h₁₂ : f (w₁ + w₂) F.s = 0 := by simp [map_add, h₁, h₂]
  apply Units.ext
  rw [F.siegel_coe_toMatrix' h₁₂, Matrix.GeneralLinearGroup.coe_mul,
    F.siegel_coe_toMatrix' h₁, F.siegel_coe_toMatrix' h₂, ← LinearMap.toMatrix'_mul,
    ← F.siegelLin_add h₁ h₂]

theorem siegel_neg {w : Fin m → ZMod p} (hw : f w F.s = 0) : F.siegel (-w) = (F.siegel w)⁻¹ := by
  have hneg : f (-w) F.s = 0 := by simpa using hw
  have h := (F.siegel_add hneg hw).symm
  rw [neg_add_cancel, F.siegel_zero] at h
  exact eq_inv_of_mul_eq_one_left h

theorem siegel_nsmul {w : Fin m → ZMod p} (hw : f w F.s = 0) (n : ℕ) :
    F.siegel (n • w) = F.siegel w ^ n := by
  induction n with
  | zero => simp [F.siegel_zero]
  | succ n ih =>
    have hn : f (n • w) F.s = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) n w, map_smul, LinearMap.smul_apply, hw,
        smul_zero]
    rw [add_smul, one_smul, F.siegel_add hn hw, ih, pow_succ]

theorem siegel_eq_one_iff {w : Fin m → ZMod p} (hw : w ∈ F.U) : F.siegel w = 1 ↔ w = 0 := by
  constructor
  · intro h
    have hval := congrArg (fun g : GL (Fin m) (ZMod p) =>
      ((g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.s')) h
    rw [F.siegel_mulVec hw.1] at hval
    simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at hval
    have hs's : f F.s' F.s = 1 := by rw [F.symm, F.pair]
    have hs'w : f F.s' w = 0 := by rw [F.symm]; exact hw.2
    rw [hs's, hs'w] at hval
    simp only [one_smul, zero_smul, sub_zero, mul_one] at hval
    have hw_eq : w = (2⁻¹ * f w w) • F.s := by
      have h' : F.s' + (w - (2⁻¹ * f w w) • F.s) = F.s' + 0 := by
        simpa [sub_eq_add_neg, add_assoc] using hval
      exact sub_eq_zero.1 (add_left_cancel h')
    have hc : (2⁻¹ * f w w) = 0 := by
      have hw2 : f w F.s' = 0 := hw.2
      have hf := congrArg (fun z => f z F.s') hw_eq
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, F.pair, mul_one, hw2] at hf
      exact hf.symm
    rw [hc, zero_smul] at hw_eq
    exact hw_eq
  · intro hw0
    rw [hw0]
    exact F.siegel_zero

private theorem orthRefl_coe_toMatrix' {v : Fin m → ZMod p} (hv : f v v = -2) :
    (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) = LinearMap.toMatrix' (orthReflLin f v) := by
  rw [orthRefl]
  split_ifs with h
  · rfl
  · exact absurd hv h

private theorem isOrthIsometry_inv_apply {g : GL (Fin m) (ZMod p)} (hg : IsOrthIsometry f g)
    (x y : Fin m → ZMod p) :
    f ((↑g⁻¹ : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) y =
      f x ((↑g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ y) := by
  have h := hg ((↑g⁻¹ : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) y
  rw [show (↑g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ
      ((↑g⁻¹ : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) = x by
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]] at h
  exact h.symm

theorem siegel_neg_smul {v : Fin m → ZMod p} (hv : f v v = -2) (hvs : f v F.s = 0) (c : ZMod p) :
    F.siegel (-(c • v)) = orthRefl f v * orthRefl f (v + c • F.s) := by
  have hsv : f F.s v = 0 := (F.symm v F.s).symm.trans hvs
  have hvc : f (v + c • F.s) (v + c • F.s) = -2 := by
    simp [map_add, map_smul, hvs, hsv, F.isotropic_s, hv]
  have hneg : f (-(c • v)) F.s = 0 := by
    simp [map_smul, hvs]
  have hlin : F.siegelLin (-(c • v)) = orthReflLin f v * orthReflLin f (v + c • F.s) := by
    have h2 : (2 : ZMod p)⁻¹ * (-2) = -1 := by
      rw [show (-2 : ZMod p) = -(2 * 1) by ring, mul_neg, mul_one, inv_mul_cancel₀ F.two_ne]
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, F.siegelLin_apply, orthReflLin_apply, orthReflLin_apply]
    simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, smul_eq_mul, hv, hsv]
    match_scalars
    all_goals
      first
      | field_simp [F.two_ne]
        ring
      | ring
  apply Units.ext
  rw [F.siegel_coe_toMatrix' hneg, Matrix.GeneralLinearGroup.coe_mul,
    orthRefl_coe_toMatrix' hv, orthRefl_coe_toMatrix' hvc, ← LinearMap.toMatrix'_mul, hlin]

theorem siegel_conj {g : GL (Fin m) (ZMod p)} (hg : IsOrthIsometry f g)
    (hgs : (g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ F.s = F.s) (w : Fin m → ZMod p) :
    g * F.siegel w * g⁻¹ = F.siegel ((g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) := by
  by_cases hw : f w F.s = 0
  · have hgw : f ((↑g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) F.s = 0 := by
      have h := hg w F.s
      rwa [hgs, hw] at h
    have hgg : ∀ x, (↑g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ
        ((↑g⁻¹ : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) = x := by
      intro x
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro x
    have h1 : f ((↑g⁻¹ : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) F.s = f x F.s := by
      rw [isOrthIsometry_inv_apply hg x F.s, hgs]
    have h2 : f ((↑g⁻¹ : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) w =
        f x ((↑g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) :=
      isOrthIsometry_inv_apply hg x w
    have h3 : f ((↑g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w)
        ((↑g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) = f w w := hg w w
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.siegel_mulVec hw,
      F.siegel_mulVec hgw]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hgg x, hgs,
      h1, h2, h3]
  · have hgw : f ((↑g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ w) F.s ≠ 0 := by
      intro h
      have hh := hg w F.s
      rw [hgs, h] at hh
      exact hw hh.symm
    simp [siegel, dif_neg hw, dif_neg hgw]

@[expose] def siegelHom : Multiplicative F.U →* GL (Fin m) (ZMod p) where
  toFun w := F.siegel ((Multiplicative.toAdd w : F.U) : Fin m → ZMod p)
  map_one' := by
    simpa using F.siegel_zero
  map_mul' w₁ w₂ := by
    rw [toAdd_mul, Submodule.coe_add]
    exact F.siegel_add (F.mem_U.1 (Multiplicative.toAdd w₁).2).1
      (F.mem_U.1 (Multiplicative.toAdd w₂).2).1

@[expose] def Y : Subgroup (GL (Fin m) (ZMod p)) := F.siegelHom.range

theorem mem_Y {g : GL (Fin m) (ZMod p)} : g ∈ F.Y ↔ ∃ w ∈ F.U, F.siegel w = g := by
  constructor
  · intro hg
    rw [Y, MonoidHom.mem_range] at hg
    obtain ⟨a, ha⟩ := hg
    refine ⟨((Multiplicative.toAdd a : F.U) : Fin m → ZMod p), (Multiplicative.toAdd a).2, ?_⟩
    exact ha
  · rintro ⟨w, hw, rfl⟩
    rw [Y, MonoidHom.mem_range]
    exact ⟨Multiplicative.ofAdd ⟨w, hw⟩, rfl⟩

@[expose] def refl : GL (Fin m) (ZMod p) := orthRefl f F.a

@[expose] def Z : Subgroup (GL (Fin m) (ZMod p)) :=
  F.Y ⊓ Subgroup.centralizer
    ((Subgroup.zpowers F.refl : Subgroup (GL (Fin m) (ZMod p))) : Set (GL (Fin m) (ZMod p)))

end OrthFrame

end CFSG.LocalAnalysis.WeakClosure81
