module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameModule
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCfg
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordStd
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCoordA
import Mathlib.Algebra.Group.TypeTags.Basic

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

open scoped Matrix

variable {G : Type} [Group G] [Finite G]

structure QTwoUnitCoords (Bs : Subgroup G) (x : G) (L : Subgroup G) (𝒦 : Finset (Subgroup G))
    {ι : Type} (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) {m : ℕ}
    (e' : Fin m ≃ ι) {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] (ψ : Su F0 2 1 m →* G)
    (ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)) (βL : Additive ↥Bs ≃+ DVec m) (ω : F0ˣ) :
    Prop where
  ω_order : orderOf ω = 3
  x_coord : ∀ hx : x ∈ Bs, βL (Additive.ofMul ⟨x, hx⟩) = fun _ => 1
  induces : ∀ s : ↥Bs,
    qTwoChartTwoThree_induces ψ (s : G) (fun i => ω ^ (βL (Additive.ofMul s) i).val)
  perm : ∀ (σ : Equiv.Perm (Fin m)) (s : ↥Bs),
    βL (Additive.ofMul ((((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) s)) =
      dPerm m σ (βL (Additive.ofMul s))
  join_onto : ∀ w ∈ dEven m, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
    ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s))
  cox : ∀ (sgn : Bool) (a b : Fin m), a ≠ b → ∀ r ∈ ggAutomizerJoin L Bs 𝒦,
    (∀ s : ↥Bs, βL (Additive.ofMul (r s)) = dTau m sgn a b (βL (Additive.ofMul s))) →
      r ∈ ggCoxRefl M e
  coxRoot : ∀ r ∈ ggCoxRefl M e, ∃ (sgn : Bool) (a b : Fin m), a ≠ b ∧ ∀ s : ↥Bs,
    βL (Additive.ofMul (r s)) = dTau m sgn a b (βL (Additive.ofMul s))
  node : ∃ c₀ : Fin m, ∀ i : Fin m, (i : ℕ) ≠ 0 → ∃ (sgn : Bool) (a b : Fin m),
    a ≠ b ∧ a ≠ c₀ ∧ b ≠ c₀ ∧ ∀ s : ↥Bs,
      βL (Additive.ofMul ((((e (M.simple (e' i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
        s)) = dTau m sgn a b (βL (Additive.ofMul s))


attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {m : ℕ}

lemma qtwoDB19_sign_decide {x : ZMod 3} (hx : x = 1 ∨ x = -1) :
    (if decide (x = -1) then (-1 : ZMod 3) else 1) = x := by
  rcases hx with h | h <;> rw [h] <;> decide

lemma qtwoDB19_inv_basis {P : DVec m ≃ₗ[ZMod 3] DVec m}
    {π : Equiv.Perm (Fin m)} {t : Fin m → ZMod 3} (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hP : ∀ i, P (dBasis m i) = t i • dBasis m (π i)) (i : Fin m) :
    P⁻¹ (dBasis m (π i)) = t i • dBasis m i := by
  have hsq : t i * t i = 1 := by rcases ht i with h | h <;> rw [h] <;> decide
  have h1 : P (t i • dBasis m i) = dBasis m (π i) := by
    rw [map_smul, hP i, smul_smul, hsq, one_smul]
  rw [← h1]
  exact LinearEquiv.symm_apply_apply P (t i • dBasis m i)

lemma qtwoDB19_inv_basis' {P : DVec m ≃ₗ[ZMod 3] DVec m}
    {π : Equiv.Perm (Fin m)} {t : Fin m → ZMod 3} (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hP : ∀ i, P (dBasis m i) = t i • dBasis m (π i)) (i : Fin m) :
    P⁻¹ (dBasis m i) = t (π⁻¹ i) • dBasis m (π⁻¹ i) := by
  rw [show dBasis m i = dBasis m (π (π⁻¹ i)) from
    congrArg (dBasis m) (Equiv.apply_symm_apply π i).symm]
  exact qtwoDB19_inv_basis ht hP (π⁻¹ i)

theorem qtwoDB19_conj_mem_dEven {P : DVec m ≃ₗ[ZMod 3] DVec m}
    {π : Equiv.Perm (Fin m)} {t : Fin m → ZMod 3} (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hP : ∀ i, P (dBasis m i) = t i • dBasis m (π i))
    {g : DVec m ≃ₗ[ZMod 3] DVec m} (hg : g ∈ dEven m) :
    P * g * P⁻¹ ∈ dEven m := by
  obtain ⟨σ, c, hc, hprod, hact⟩ := hg
  have hsq : ∀ i, t i * t i = 1 := fun i => by rcases ht i with h | h <;> rw [h] <;> decide
  have htsq : (∏ i, t i) * (∏ i, t i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => hsq i
  refine ⟨π * σ * π⁻¹, fun i => c (π⁻¹ i) * (t (π⁻¹ i) * t (σ (π⁻¹ i))), ?_, ?_, ?_⟩
  · intro i
    change c (π⁻¹ i) * (t (π⁻¹ i) * t (σ (π⁻¹ i))) = 1 ∨
      c (π⁻¹ i) * (t (π⁻¹ i) * t (σ (π⁻¹ i))) = -1
    rcases hc (π⁻¹ i) with h | h <;> rcases ht (π⁻¹ i) with h' | h' <;>
      rcases ht (σ (π⁻¹ i)) with h'' | h'' <;> rw [h, h', h''] <;> decide
  · rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Equiv.prod_comp π⁻¹ c,
      Equiv.prod_comp π⁻¹ t, Equiv.prod_comp π⁻¹ (fun i => t (σ i)),
      Equiv.prod_comp σ t, hprod, htsq]
    simp
  · intro i
    change (P * g * P⁻¹) (dBasis m i) = _
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, qtwoDB19_inv_basis' ht hP i,
      map_smul, hact (π⁻¹ i), map_smul, map_smul, hP (σ (π⁻¹ i)), smul_smul, smul_smul]
    rw [show t (π⁻¹ i) * c (π⁻¹ i) * t (σ (π⁻¹ i)) =
      c (π⁻¹ i) * (t (π⁻¹ i) * t (σ (π⁻¹ i))) by ring]
    rfl

theorem qtwoDB19_conj_dTau {P : DVec m ≃ₗ[ZMod 3] DVec m}
    {π : Equiv.Perm (Fin m)} {t : Fin m → ZMod 3} (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hP : ∀ i, P (dBasis m i) = t i • dBasis m (π i))
    (sgn : Bool) {a b : Fin m} (hab : a ≠ b) :
    ∃ sgn' : Bool, P * dTau m sgn a b * P⁻¹ = dTau m sgn' (π a) (π b) := by
  have hpia : π a ≠ π b := fun h => hab (π.injective h)
  have hcase : t a * (if sgn then (-1 : ZMod 3) else 1) * t b = 1 ∨
      t a * (if sgn then (-1 : ZMod 3) else 1) * t b = -1 := by
    rcases ht a with h | h <;> rcases ht b with h' | h' <;> cases sgn <;>
      simp [h, h']
  refine ⟨decide (t a * (if sgn then (-1 : ZMod 3) else 1) * t b = -1), ?_⟩
  refine (dBasis m).ext' fun k => ?_
  obtain ⟨i, rfl⟩ := π.surjective k
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, qtwoDB19_inv_basis ht hP i, map_smul]
  by_cases hia : i = a
  · rw [hia] at *
    rw [dTau_apply_left m sgn hab, map_smul, map_smul, hP b, dTau_apply_left m _ hpia]
    simp only [smul_smul]
    rw [qtwoDB19_sign_decide hcase]
    ring
  · by_cases hib : i = b
    · rw [hib] at *
      rw [dTau_apply_right m sgn hab, map_smul, map_smul, hP a, dTau_apply_right m _ hpia]
      simp only [smul_smul]
      rw [qtwoDB19_sign_decide hcase]
      rw [show t b * ((if sgn then (-1 : ZMod 3) else 1) * t a) =
          (t a * (if sgn then (-1 : ZMod 3) else 1)) * t b by ring_nf]
    · rw [dTau_apply_of_ne m sgn hia hib, map_smul, hP i, smul_smul,
        show t i * t i = 1 by rcases ht i with h | h <;> rw [h] <;> decide, one_smul]
      exact (dTau_apply_of_ne m _ (fun h => hia (π.injective h))
        (fun h => hib (π.injective h))).symm

section Helpers

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {Bs L : Subgroup G} {x : G}

lemma qtwoDB19_dPerm_eval (σ : Equiv.Perm (Fin m)) (v : DVec m) (i : Fin m) :
    dPerm m σ v i = v (σ.symm i) := by
  have hlin : (LinearMap.proj i).comp (dPerm m σ : DVec m →ₗ[ZMod 3] DVec m) =
      LinearMap.proj (σ.symm i) := by
    refine (dBasis m).ext fun k => ?_
    change (dPerm m σ (dBasis m k)) i = (dBasis m k) (σ.symm i)
    rw [dPerm_apply]
    simp only [dBasis, Pi.basisFun_apply]
    by_cases h : σ k = i
    · rw [h, show σ.symm i = k from by rw [← h, Equiv.symm_apply_apply],
        Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (show i ≠ σ k from fun hh => h hh.symm),
        Pi.single_eq_of_ne (show σ.symm i ≠ k from fun hh => h (by
          rw [← hh, Equiv.apply_symm_apply]))]
  have := congrArg (fun f : DVec m →ₗ[ZMod 3] ZMod 3 => f v) hlin
  simpa [LinearMap.comp_apply, LinearMap.proj_apply] using this

lemma qtwoDB19_ggPermSU_mulVec (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single i 1 = Pi.single (σ i) 1 := by
  rw [show ((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) =
      (σ⁻¹).permMatrix F0 from rfl, Matrix.permMatrix_mulVec]
  funext j
  simp only [Function.comp_apply, Pi.single_apply]
  exact if_congr (Equiv.symm_apply_eq σ) rfl rfl

lemma qtwoDB19_diag_const_comm (lam : F0ˣ) (u : GL (Fin m) F0) :
    qTwoChartTwoThree_diag (fun _ : Fin m => lam) * u =
      u * qTwoChartTwoThree_diag (fun _ : Fin m => lam) := by
  apply Units.ext
  simp only [Units.val_mul, qTwoChartTwoThree_diag]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

lemma qtwoDB19_induces_scalar_iff {ψ : Su F0 2 1 m →* G} {b : G} {c : Fin m → F0ˣ}
    (lam : F0ˣ) :
    qTwoChartTwoThree_induces ψ b (fun i => lam * c i) ↔
      qTwoChartTwoThree_induces ψ b c := by
  have hD : qTwoChartTwoThree_diag (fun i => lam * c i) =
      qTwoChartTwoThree_diag (fun _ : Fin m => lam) * qTwoChartTwoThree_diag c :=
    qtwoDB19_diag_mul (fun _ : Fin m => lam) c
  constructor
  · intro h u
    obtain ⟨u', hu'mat, hu'ψ⟩ := h u
    refine ⟨u', ?_, hu'ψ⟩
    rw [hu'mat, hD, mul_inv_rev]
    rw [show (qTwoChartTwoThree_diag (fun _ : Fin m => lam) * qTwoChartTwoThree_diag c) *
        (u : GL (Fin m) F0) *
        ((qTwoChartTwoThree_diag c)⁻¹ * (qTwoChartTwoThree_diag (fun _ : Fin m => lam))⁻¹) =
        qTwoChartTwoThree_diag (fun _ : Fin m => lam) *
          (qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
            (qTwoChartTwoThree_diag c)⁻¹) *
          (qTwoChartTwoThree_diag (fun _ : Fin m => lam))⁻¹ by group]
    rw [qtwoDB19_diag_const_comm lam]
    group
  · intro h u
    obtain ⟨u', hu'mat, hu'ψ⟩ := h u
    refine ⟨u', ?_, hu'ψ⟩
    rw [hu'mat, hD, mul_inv_rev]
    rw [show (qTwoChartTwoThree_diag (fun _ : Fin m => lam) * qTwoChartTwoThree_diag c) *
        (u : GL (Fin m) F0) *
        ((qTwoChartTwoThree_diag c)⁻¹ * (qTwoChartTwoThree_diag (fun _ : Fin m => lam))⁻¹) =
        qTwoChartTwoThree_diag (fun _ : Fin m => lam) *
          (qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
            (qTwoChartTwoThree_diag c)⁻¹) *
          (qTwoChartTwoThree_diag (fun _ : Fin m => lam))⁻¹ by group]
    rw [qtwoDB19_diag_const_comm lam]
    group

lemma qtwoDB19_pow_val_add {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {γ : F0ˣ} (hγ : orderOf γ = 3) (a b : ZMod 3) :
    γ ^ (a + b).val = γ ^ a.val * γ ^ b.val := by
  rw [← pow_add, pow_eq_pow_iff_modEq, hγ]
  show (a + b).val % 3 = (a.val + b.val) % 3
  rw [ZMod.val_add]
  exact Nat.mod_mod _ _

lemma qtwoDB19_pow_val_mul {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {γ : F0ˣ} (hγ : orderOf γ = 3) (a b : ZMod 3) :
    γ ^ (a * b).val = (γ ^ a.val) ^ b.val := by
  rw [← pow_mul, pow_eq_pow_iff_modEq, hγ]
  show (a * b).val % 3 = a.val * b.val % 3
  rw [ZMod.val_mul]
  exact Nat.mod_mod _ _

lemma qtwoDB19_ggLin_trans {Bs : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m)
    (P : DVec m ≃ₗ[ZMod 3] DVec m) (φ : MulAut ↥Bs) :
    ggLin (p := 3) (β.trans P.toAddEquiv) φ = P * ggLin (p := 3) β φ * P⁻¹ := by
  refine LinearEquiv.ext fun v => ?_
  rw [ggLin_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggLin_apply]
  rfl

end Helpers

end CFSG.StandardType.QTwo

end
