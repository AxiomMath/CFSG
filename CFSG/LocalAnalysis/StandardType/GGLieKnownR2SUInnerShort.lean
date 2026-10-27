module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSUShort
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUPCore

public section

namespace CFSG.StandardType.LieKnownR2.PSU

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Unitary (antidiag conjTr)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open scoped Matrix

private theorem l10su2_semilinear {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (y : MulAut ↥(Unitary.SU (unitaryInvolution F 2 f) n)) (A : GL (Fin n) F) (φ : F ≃+* F)
    (hyA : ∀ x : ↥(Unitary.SU (unitaryInvolution F 2 f) n),
      ((y x : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) =
        A * glAut φ (x : GL (Fin n) F) * A⁻¹)
    (g : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) (x : Fin n → F) :
    (((y g : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) *ᵥ ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (x i)) =
      (A : Matrix (Fin n) (Fin n) F) *ᵥ
        fun i => φ ((((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ x) i) := by
  have hcoe : (((A * glAut φ (g : GL (Fin n) F) * A⁻¹ : GL (Fin n) F)) :
      Matrix (Fin n) (Fin n) F) =
      (A : Matrix (Fin n) (Fin n) F) *
        ((glAut φ (g : GL (Fin n) F) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  have hAA : ((A : Matrix (Fin n) (Fin n) F)⁻¹ * (A : Matrix (Fin n) (Fin n) F)) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  rw [hyA g, hcoe, Matrix.GeneralLinearGroup.coe_inv]
  rw [Matrix.mulVec_mulVec, mul_assoc, hAA, mul_one, ← Matrix.mulVec_mulVec]
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coe_glAut]
  congr 1
  funext i
  exact (RingHom.map_mulVec (φ : F →+* F) ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) x i).symm

private theorem l10su2_mem_span {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : Short.SUFrame hF n v w v' w')
    (y : MulAut ↥(Unitary.SU (unitaryInvolution F 2 f) n))
    (hyR : (Short.suPair (unitaryInvolution F 2 f) n v w).map y.toMonoidHom =
      Short.suPair (unitaryInvolution F 2 f) n v w)
    (A : GL (Fin n) F) (φ : F ≃+* F)
    (hyA : ∀ x : ↥(Unitary.SU (unitaryInvolution F 2 f) n),
      ((y x : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) =
        A * glAut φ (x : GL (Fin n) F) * A⁻¹) :
    (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (v i)) ∈ Submodule.span F {v, w} ∧
      (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (w i)) ∈ Submodule.span F {v, w} := by
  have hv : (Short.suH hF n).β v v = 0 := hfr.2.2.1.1
  have hw : (Short.suH hF n).β w w = 0 := hfr.2.2.1.2.1
  have hvw : (Short.suH hF n).β v w = 0 := hfr.2.2.2.1
  obtain ⟨T, hTmem, hT⟩ := Short.exists_mem_suPair_mulVec hF hv hw hvw (1 : F)
  have hyTmem : y T ∈ Short.suPair (unitaryInvolution F 2 f) n v w := by
    rw [← hyR]
    exact Subgroup.mem_map_of_mem y.toMonoidHom hTmem
  obtain ⟨a, ha⟩ := Short.exists_mulVec_of_mem_suPair hF hv hw hvw hyTmem
  have key : ∀ (z z' : Fin n → F),
      (((T : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ z') = z' + z →
      (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (z i)) ∈ Submodule.span F {v, w} := by
    intro z z' hzz'
    have hs := l10su2_semilinear y A φ hyA T z'
    rw [hzz'] at hs
    have hphi : (fun i => φ ((z' + z) i)) =
        (fun i => φ (z' i)) + (fun i => φ (z i)) := by
      funext i; simp [map_add]
    rw [hphi, Matrix.mulVec_add] at hs
    have ha' := ha ((A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (z' i)))
    rw [natRep_apply] at ha'
    rw [ha'] at hs
    have hrest : (a * (Short.suH hF n).β w
          ((A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (z' i)))) • v +
        ((unitaryInvolution F 2 f) a * (Short.suH hF n).β v
          ((A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (z' i)))) • w =
        (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (z i)) := by
      have h := hs
      rw [add_assoc] at h
      exact add_left_cancel h
    rw [← hrest]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hvv' : (((T : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *ᵥ v' = v' + v := by
    have h := hT v'
    rw [natRep_apply] at h
    simpa [hfr.2.1, hfr.2.2.2.2.1] using h
  have hww' : (((T : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *ᵥ w' = w' + w := by
    have h := hT w'
    rw [natRep_apply] at h
    simpa [hfr.1, hfr.2.2.2.2.2.1] using h
  exact ⟨key v v' hvv', key w w' hww'⟩

private theorem l10su2_phi_eigen {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {v w v' w' : Fin n → F} (hfr : Short.SUFrame hF n v w v' w')
    (y : MulAut ↥(Unitary.SU (unitaryInvolution F 2 f) n))
    (hyR : (Short.suPair (unitaryInvolution F 2 f) n v w).map y.toMonoidHom =
      Short.suPair (unitaryInvolution F 2 f) n v w)
    (hy : ∀ m ∈ Subgroup.normalizer
        (Short.suPair (unitaryInvolution F 2 f) n v w :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n)),
      y m * m⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer
          (Short.suPair (unitaryInvolution F 2 f) n v w :
            Set ↥(Unitary.SU (unitaryInvolution F 2 f) n))) ⊔
        Subgroup.center ↥(Unitary.SU (unitaryInvolution F 2 f) n))
    (A : GL (Fin n) F) (φ : F ≃+* F)
    (hyA : ∀ x : ↥(Unitary.SU (unitaryInvolution F 2 f) n),
      ((y x : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) =
        A * glAut φ (x : GL (Fin n) F) * A⁻¹)
    {c : F} (hc : c ≠ 0) : φ c = c ∨ φ c * c = 1 := by
  obtain ⟨t, htv, htw, -, -, -⟩ :=
    Short.exists_mem_SU_torus hfr (μ := c) (ν := c⁻¹) hc (inv_ne_zero hc)
      (by rw [mul_inv_cancel₀ hc, map_one])
  have htN : t ∈ Subgroup.normalizer
      (Short.suPair (unitaryInvolution F 2 f) n v w :
        Set ↥(Unitary.SU (unitaryInvolution F 2 f) n)) := by
    rw [Short.mem_normalizer_suPair_iff hfr]
    exact Or.inl ⟨c, c⁻¹, htv, htw⟩
  obtain ⟨r, hr, z, hz, hrz⟩ := Subgroup.mem_sup_of_normal_right.mp (hy t htN)
  have hyt : y t = r * z * t := by
    rw [hrz, mul_assoc, inv_mul_cancel, mul_one]
  have hrW : ∀ x ∈ Submodule.span F {v, w},
      natRep (Unitary.SU (unitaryInvolution F 2 f) n) r x = x := by
    intro x hx
    have hrR : r ∈ Short.suStabRad hF n (Submodule.span F {v, w})
        (Short.suFrame_isTotallyIsotropic hfr) :=
      Short.pCoreOf_normalizer_suPair_le_suStabRad hfr hr
    rw [Short.suStabRad] at hrR
    exact (CFSG.QuasithinUnique.B113Lie.Sp.mem_rad.mp hrR).1 x hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζu, hζu⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_scalar_of_mem_center_SU
      (p := 2) hF (by omega) hnq hz
  set ζ : F := (ζu : F) with hζdef
  have hζ0 : ζ ≠ 0 := by rw [hζdef]; exact Units.ne_zero ζu
  have hzW : ∀ x : Fin n → F, natRep (Unitary.SU (unitaryInvolution F 2 f) n) z x = ζ • x := by
    intro x
    rw [natRep_apply, hζu, Matrix.GeneralLinearGroup.coe_scalar, hζdef]
    funext i
    simp [Matrix.mulVec, Matrix.scalar_apply, Pi.smul_apply, smul_eq_mul]
  obtain ⟨hmemv, hmemw⟩ := l10su2_mem_span hF hfr y hyR A φ hyA
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmemv
  obtain ⟨α', β', hα'β'⟩ := Submodule.mem_span_pair.mp hmemw
  have hv0 : v ≠ 0 := by
    intro h0
    have h := hfr.1
    rw [h0, (Short.suH hF n).β_zero_left] at h
    exact zero_ne_one h
  have hw0 : w ≠ 0 := by
    intro h0
    have h := hfr.2.1
    rw [h0, (Short.suH hF n).β_zero_left] at h
    exact zero_ne_one h
  have hAA : (((A⁻¹ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
      (A : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hker : ∀ x : Fin n → F, (A : Matrix (Fin n) (Fin n) F) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h := congrArg
      (fun u => (((A⁻¹ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *ᵥ u) hx
    rw [Matrix.mulVec_zero] at h
    rwa [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec] at h
  have hvwind : ∀ a b : F, a • v + b • w = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    constructor
    · have h := congrArg (fun u => (Short.suH hF n).β u w') hab
      rw [(Short.suH hF n).add_left, (Short.suH hF n).smul_left,
        (Short.suH hF n).smul_left, (Short.suH hF n).β_zero_left,
        hfr.1, hfr.2.2.2.2.2.1, mul_one, mul_zero, add_zero] at h
      exact (map_eq_zero_iff _ (unitaryInvolution F 2 f).injective).mp h
    · have h := congrArg (fun u => (Short.suH hF n).β u v') hab
      rw [(Short.suH hF n).add_left, (Short.suH hF n).smul_left,
        (Short.suH hF n).smul_left, (Short.suH hF n).β_zero_left,
        hfr.2.2.2.2.1, hfr.2.1, mul_zero, mul_one, zero_add] at h
      exact (map_eq_zero_iff _ (unitaryInvolution F 2 f).injective).mp h
  have hcoeff : ∀ {a₁ a₂ b₁ b₂ : F},
      a₁ • v + b₁ • w = a₂ • v + b₂ • w → a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ a₂ b₁ b₂ h
    have h0 : (a₁ - a₂) • v + (b₁ - b₂) • w = 0 := by
      have h1 : (a₁ - a₂) • v + (b₁ - b₂) • w =
          (a₁ • v + b₁ • w) - (a₂ • v + b₂ • w) := by
        rw [sub_smul, sub_smul]; abel
      rw [h1, h, sub_self]
    obtain ⟨ha, hb⟩ := hvwind (a₁ - a₂) (b₁ - b₂) h0
    exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb⟩
  have hind : ∀ a b : F,
      a • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) +
        b • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) = 0 →
      a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 : (A : Matrix (Fin n) (Fin n) F) *ᵥ
        (a • (fun i => φ (v i)) + b • (fun i => φ (w i))) = 0 := by
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add] at hab
      exact hab
    have h2 : a • (fun i => φ (v i)) + b • (fun i => φ (w i)) = 0 := by
      have h := congrArg
        (fun u => (((A⁻¹ : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *ᵥ u) h1
      rw [Matrix.mulVec_zero] at h
      rwa [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec] at h
    have h3 : (φ.symm a) • v + (φ.symm b) • w = 0 := by
      funext i
      have hi := congrFun h2 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      have h4 := congrArg φ.symm hi
      simp only [map_add, map_mul, map_zero, RingEquiv.apply_symm_apply] at h4
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h4
    obtain ⟨ha, hb⟩ := hvwind (φ.symm a) (φ.symm b) h3
    exact ⟨by simpa using congrArg φ ha, by simpa using congrArg φ hb⟩
  have hBvne : (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (v i)) ≠ 0 := by
    intro h
    apply hv0
    have hφv : (fun i => φ (v i)) = 0 := hker _ h
    funext i
    have := congrFun hφv i
    simpa using congrArg φ.symm this
  have hBwne : (A : Matrix (Fin n) (Fin n) F) *ᵥ (fun i => φ (w i)) ≠ 0 := by
    intro h
    apply hw0
    have hφw : (fun i => φ (w i)) = 0 := hker _ h
    funext i
    have := congrFun hφw i
    simpa using congrArg φ.symm this
  have htBv : natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
      ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) =
      α • (c • v) + β • (c⁻¹ • w) := by
    rw [← hαβ, map_add, map_smul, map_smul, htv, htw]
  have htBw : natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
      ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) =
      α' • (c • v) + β' • (c⁻¹ • w) := by
    rw [← hα'β', map_add, map_smul, map_smul, htv, htw]
  have htBv_mem : natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
      ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) ∈ Submodule.span F {v, w} := by
    rw [htBv]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  have htBw_mem : natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
      ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) ∈ Submodule.span F {v, w} := by
    rw [htBw]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  have hstruct_v : natRep (Unitary.SU (unitaryInvolution F 2 f) n) (y t)
      ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) =
      ζ • natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
        ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) := by
    rw [hyt]
    simp only [map_mul, Module.End.mul_apply]
    rw [hzW (natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
        ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i))), map_smul, hrW _ htBv_mem]
  have hstruct_w : natRep (Unitary.SU (unitaryInvolution F 2 f) n) (y t)
      ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) =
      ζ • natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
        ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) := by
    rw [hyt]
    simp only [map_mul, Module.End.mul_apply]
    rw [hzW (natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
        ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i))), map_smul, hrW _ htBw_mem]
  have hsemi_v : natRep (Unitary.SU (unitaryInvolution F 2 f) n) (y t)
      ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) =
      φ c • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) := by
    have hs := l10su2_semilinear y A φ hyA t v
    have htmat : (((t : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *ᵥ v = c • v := by
      have h := htv
      rwa [natRep_apply] at h
    rw [natRep_apply, hs, htmat]
    have hphi : (fun i => φ ((c • v) i)) = φ c • (fun i => φ (v i)) := by
      funext i; simp [Pi.smul_apply, map_mul]
    rw [hphi, Matrix.mulVec_smul]
  have hsemi_w : natRep (Unitary.SU (unitaryInvolution F 2 f) n) (y t)
      ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) =
      (φ c)⁻¹ • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) := by
    have hs := l10su2_semilinear y A φ hyA t w
    have htmat : (((t : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *ᵥ w = c⁻¹ • w := by
      have h := htw
      rwa [natRep_apply] at h
    rw [natRep_apply, hs, htmat]
    have hphi : (fun i => φ ((c⁻¹ • w) i)) = (φ c)⁻¹ • (fun i => φ (w i)) := by
      funext i; simp [Pi.smul_apply, map_mul, map_inv₀]
    rw [hphi, Matrix.mulVec_smul]
  have heq_v : φ c • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) =
      ζ • natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
        ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) := by
    rw [← hsemi_v, hstruct_v]
  have heq_w : (φ c)⁻¹ • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) =
      ζ • natRep (Unitary.SU (unitaryInvolution F 2 f) n) t
        ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) := by
    rw [← hsemi_w, hstruct_w]
  have hEqv : (φ c * α) • v + (φ c * β) • w =
      (ζ * α * c) • v + (ζ * β * c⁻¹) • w := by
    have h := heq_v
    rw [htBv, ← hαβ] at h
    simpa only [smul_add, smul_smul, mul_assoc] using h
  obtain ⟨hα_eq, hβ_eq⟩ := hcoeff hEqv
  have hEqw : ((φ c)⁻¹ * α') • v + ((φ c)⁻¹ * β') • w =
      (ζ * α' * c) • v + (ζ * β' * c⁻¹) • w := by
    have h := heq_w
    rw [htBw, ← hα'β'] at h
    simpa only [smul_add, smul_smul, mul_assoc] using h
  obtain ⟨hα'_eq, hβ'_eq⟩ := hcoeff hEqw
  set u : F := φ c with hu
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact fun h => hc (φ.injective (by rw [h, map_zero]))
  have hIeq : α * u = α * (ζ * c) := by
    rw [hu, mul_comm α, hα_eq]; ring
  have hIIeq : β * u = β * (ζ * c⁻¹) := by
    rw [hu, mul_comm β, hβ_eq]; ring
  have hIIIeq : α' * u⁻¹ = α' * (ζ * c) := by
    rw [hu, mul_comm α', hα'_eq]; ring
  have hIVeq : β' * u⁻¹ = β' * (ζ * c⁻¹) := by
    rw [hu, mul_comm β', hβ'_eq]; ring
  have hαβ_ne : α ≠ 0 ∨ β ≠ 0 := by
    by_contra h; push Not at h
    apply hBvne
    rw [← hαβ, h.1, h.2, zero_smul, zero_smul, add_zero]
  have hcross : α * β' ≠ 0 ∨ α' * β ≠ 0 := by
    by_contra hc'
    push Not at hc'
    obtain ⟨h1, h2⟩ := hc'
    have hcomb1 : β' • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) +
        β • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) = 0 := by
      rw [← hαβ, ← hα'β']
      simp only [smul_add, smul_smul]
      rw [mul_comm β' α, mul_comm β α', h1, h2]
      simp only [zero_smul, zero_add]
      rw [mul_comm β β', ← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    have hcomb2 : α' • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (v i)) +
        α • ((A : Matrix (Fin n) (Fin n) F) *ᵥ fun i => φ (w i)) = 0 := by
      rw [← hαβ, ← hα'β']
      simp only [smul_add, smul_smul]
      rw [mul_comm α' α, h2, h1]
      simp only [zero_smul, zero_add, add_zero]
      rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    obtain ⟨hβ'0, hβ0⟩ := hind β' β hcomb1
    obtain ⟨hα'0, hα0⟩ := hind α' α hcomb2
    apply hBvne
    rw [← hαβ, hα0, hβ0, zero_smul, zero_smul, add_zero]
  have hζsq : ζ * ζ = 1 := by
    rcases hcross with hne | hne
    · have hmain : α * β' * (ζ * ζ) = α * β' := by
        have hprod : (α * u) * (β' * u⁻¹) = (α * (ζ * c)) * (β' * (ζ * c⁻¹)) := by
          rw [hIeq, hIVeq]
        have hL : (α * u) * (β' * u⁻¹) = α * β' := by
          rw [show (α * u) * (β' * u⁻¹) = α * β' * (u * u⁻¹) by ring,
            mul_inv_cancel₀ hu0, mul_one]
        have hR : (α * (ζ * c)) * (β' * (ζ * c⁻¹)) = α * β' * (ζ * ζ) := by
          rw [show (α * (ζ * c)) * (β' * (ζ * c⁻¹)) = α * β' * (ζ * ζ) * (c * c⁻¹) by ring,
            mul_inv_cancel₀ hc, mul_one]
        rw [← hR, ← hprod, hL]
      have hm : α * β' * (ζ * ζ) = α * β' * 1 := by rw [hmain, mul_one]
      exact mul_left_cancel₀ hne hm
    · have hmain : α' * β * (ζ * ζ) = α' * β := by
        have hprod : (α' * u⁻¹) * (β * u) = (α' * (ζ * c)) * (β * (ζ * c⁻¹)) := by
          rw [hIIIeq, hIIeq]
        have hL : (α' * u⁻¹) * (β * u) = α' * β := by
          rw [show (α' * u⁻¹) * (β * u) = α' * β * (u⁻¹ * u) by ring,
            inv_mul_cancel₀ hu0, mul_one]
        have hR : (α' * (ζ * c)) * (β * (ζ * c⁻¹)) = α' * β * (ζ * ζ) := by
          rw [show (α' * (ζ * c)) * (β * (ζ * c⁻¹)) = α' * β * (ζ * ζ) * (c * c⁻¹) by ring,
            mul_inv_cancel₀ hc, mul_one]
        rw [← hR, ← hprod, hL]
      have hm : α' * β * (ζ * ζ) = α' * β * 1 := by rw [hmain, mul_one]
      exact mul_left_cancel₀ hne hm
  have hζ1 : ζ = 1 := by
    have hζsq' : ζ ^ 2 = 1 := by rwa [pow_two]
    rcases sq_eq_one_iff.mp hζsq' with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  rcases hαβ_ne with hα | hβ
  · left
    have hu_eq : u = ζ * c := mul_left_cancel₀ hα hIeq
    rw [hu_eq, hζ1, one_mul]
  · right
    have hu_eq : u = ζ * c⁻¹ := mul_left_cancel₀ hβ hIIeq
    rw [hu_eq, hζ1, one_mul, inv_mul_cancel₀ hc]

private theorem l10su2_phi_trivial {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (φ : F ≃+* F)
    (h : ∀ c : F, c ≠ 0 → φ c = c ∨ φ c * c = 1) : φ = RingEquiv.refl F := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Fˣ = (2 ^ f) ^ 2 - 1 := by
    haveI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  set q := 2 ^ f with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hordge : 15 ≤ orderOf g := by
    rw [hord, hcard]
    have hq16 : 16 ≤ q ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hq4 hq4
    omega
  have hg0 : (g : F) ≠ 0 := Units.ne_zero g
  have hchoice : φ (g : F) = (g : F) ∨ φ (g : F) = (g : F)⁻¹ := by
    rcases h (g : F) hg0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by
        apply mul_right_cancel₀ hg0
        rw [h1, inv_mul_cancel₀ hg0])
  rcases hchoice with hfix | hinv
  · have hψg : Units.mapEquiv φ.toMulEquiv g = g := by
      apply Units.ext
      rw [Units.coe_mapEquiv]
      exact hfix
    apply RingEquiv.ext
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · let u : Fˣ := Units.mk0 x hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      have hψu : Units.mapEquiv φ.toMulEquiv u = u := by
        rw [← hn, map_zpow, hψg]
      have : (φ (u : F)) = (u : F) := by
        have hh : ((Units.mapEquiv φ.toMulEquiv u : Fˣ) : F) = (u : F) := by rw [hψu]
        simpa [Units.coe_mapEquiv] using hh
      have huval : (u : F) = x := rfl
      rwa [huval] at this
  · exfalso
    have hg1 : (g : F) + 1 ≠ 0 := by
      intro hzero
      have hgeq : (g : F) = 1 := by
        have : (g : F) = -(1 : F) := by
          rw [eq_neg_iff_add_eq_zero]
          exact hzero
        rwa [CharTwo.neg_eq] at this
      have hgunit : g = 1 := Units.ext hgeq
      rw [hgunit, orderOf_one] at hordge
      omega
    rcases h ((g : F) + 1) hg1 with hcase | hcase
    · have h1 : (g : F)⁻¹ = (g : F) := by
        have hh := hcase
        rw [map_add, map_one, hinv] at hh
        exact add_right_cancel hh
      have h2 : (g : F) * (g : F) = 1 := by
        nth_rewrite 2 [← h1]
        exact mul_inv_cancel₀ hg0
      have h2U : g ^ 2 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
        exact h2
      have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2U
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
      omega
    · have hlin : (g : F)⁻¹ + (g : F) = 1 := by
        have hh := hcase
        rw [map_add, map_one, hinv] at hh
        have hexp : ((g : F)⁻¹ + 1) * ((g : F) + 1) = (g : F)⁻¹ + (g : F) := by
          calc ((g : F)⁻¹ + 1) * ((g : F) + 1)
              = (1 + (g : F)⁻¹) + ((g : F) + 1) := by
                rw [mul_add, mul_one, add_mul, one_mul, inv_mul_cancel₀ hg0]
                abel
            _ = (1 + 1) + ((g : F)⁻¹ + (g : F)) := by abel
            _ = (g : F)⁻¹ + (g : F) := by
                rw [CharTwo.add_self_eq_zero, zero_add]
        rwa [hexp] at hh
      have hg2 : (g : F) * (g : F) = (g : F) + 1 := by
        have hh : (g : F) * (g : F) + 1 = (g : F) := by
          have hh1 := congrArg (fun t => t * (g : F)) hlin
          rw [add_mul, inv_mul_cancel₀ hg0, one_mul] at hh1
          rw [add_comm]
          exact hh1
        have hsub := eq_sub_of_add_eq hh
        rwa [sub_eq_add_neg, CharTwo.neg_eq] at hsub
      have hcube : (g : F) ^ 3 = 1 := by
        rw [pow_three]
        calc (g : F) * ((g : F) * (g : F)) = (g : F) * ((g : F) + 1) := by rw [hg2]
          _ = (g : F) * (g : F) + (g : F) := by ring
          _ = 1 := by
              rw [hg2, add_comm ((g : F) + 1) (g : F), ← add_assoc,
                CharTwo.add_self_eq_zero, zero_add]
      have hcubeU : g ^ 3 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact hcube
      have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hcubeU
      have := Nat.le_of_dvd (by norm_num : 0 < 3) hdvd
      omega

theorem ggRootNormInnerZ_su_short {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 6 ≤ n) (hf : 2 ≤ f)
    {β : Fin (Unitary.rootDatum hF n).rank → ℤ} (hβ : β ∈ (Unitary.rootDatum hF n).roots)
    (hs : ¬ GGLongRoot (Unitary.rootDatum hF n) β)
    (h2β : 2 • β ∉ (Unitary.rootDatum hF n).roots)
    (u : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) :
    PSL.GGRootNormInnerZ
      (((Unitary.rootDatum hF n).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  intro y hy2 hyR hy
  obtain ⟨v, w, v', w', hfr, hR, -⟩ :=
    Geo.exists_unitPairGroup_eq_conj_rootGroup_SU hF n hβ hs h2β u
  have hnq : (n, 2 ^ f) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by omega)
  have hyR' : (Short.suPair (unitaryInvolution F 2 f) n v w).map y.toMonoidHom =
      Short.suPair (unitaryInvolution F 2 f) n v w := by
    rw [← hR]; exact hyR
  have hy' : ∀ m ∈ Subgroup.normalizer
        (Short.suPair (unitaryInvolution F 2 f) n v w :
          Set ↥(Unitary.SU (unitaryInvolution F 2 f) n)),
      y m * m⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer
          (Short.suPair (unitaryInvolution F 2 f) n v w :
            Set ↥(Unitary.SU (unitaryInvolution F 2 f) n))) ⊔
        Subgroup.center ↥(Unitary.SU (unitaryInvolution F 2 f) n) := by
    intro m hm
    rw [← hR] at hm ⊢
    exact hy m hm
  obtain ⟨A, φ, hA, hyA⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_conj_glAut_of_mulAut_SU hF (by omega) (by omega)
      (by rintro ⟨h1, -⟩; omega) y
  have hφ : ∀ c : F, c ≠ 0 → φ c = c ∨ φ c * c = 1 := fun c hc =>
    l10su2_phi_eigen hF (by omega) hnq hfr y hyR' hy' A φ hyA hc
  have hφ1 : φ = RingEquiv.refl F := l10su2_phi_trivial hF hf φ hφ
  have hyA1 : ∀ x : ↥(Unitary.SU (unitaryInvolution F 2 f) n),
      ((y x : ↥(Unitary.SU (unitaryInvolution F 2 f) n)) : GL (Fin n) F) =
        A * (x : GL (Fin n) F) * A⁻¹ := by
    intro x
    rw [hyA x, hφ1]
    have hgl : glAut (RingEquiv.refl F) (x : GL (Fin n) F) = (x : GL (Fin n) F) := by
      have hone : (RingEquiv.refl F) = (1 : F ≃+* F) := rfl
      rw [hone, map_one]
      rfl
    rw [hgl]
  exact inner_of_isometry hF (by omega) y hy2 A hA hyA1

end CFSG.StandardType.LieKnownR2.PSU