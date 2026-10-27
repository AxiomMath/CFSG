module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSLOrthSplit
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSLOrthNonsplit
import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowConj
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterRealUnip
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterRealPair

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private def realMat (h : UnitaryFieldData p f K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : M.map h.bar = M) : Matrix (Fin n) (Fin n) h.fixedField :=
  fun i j => ⟨M i j, h.mem_fixedField.mpr (by
    simpa [Matrix.map_apply] using congrFun (congrFun hM i) j)⟩

private theorem realMat_map (h : UnitaryFieldData p f K) {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} (hM : M.map h.bar = M) :
    (realMat h M hM).map h.fixedField.subtype = M := by
  ext i j
  simp [realMat]

private theorem realMat_det_coe (h : UnitaryFieldData p f K) {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} (hM : M.map h.bar = M) :
    ((realMat h M hM).det : K) = M.det := by
  have hd := RingHom.map_det h.fixedField.subtype (realMat h M hM)
  rw [RingHom.mapMatrix_apply] at hd
  rwa [realMat_map h hM] at hd

private theorem realMat_isUnit_det (h : UnitaryFieldData p f K) {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} (hM : M.map h.bar = M) (hunit : IsUnit M.det) :
    IsUnit (realMat h M hM).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  exact hunit.ne_zero (by simp [← realMat_det_coe h hM, h0])

private theorem self_adjoint_eq {n : ℕ} {G X : Matrix (Fin n) (Fin n) K} {m α : K}
    (hα : α ≠ 0) (hX : Xᵀ * G * X = m • G) (hX2 : X * X = α • 1) :
    Xᵀ * G = (m / α) • (G * X) := by
  have h := congrArg (fun M => M * X) hX
  rw [Matrix.mul_assoc, hX2] at h
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h
  have h' := congrArg (fun M => α⁻¹ • M) h
  rw [smul_smul, inv_mul_cancel₀ hα, one_smul, smul_smul] at h'
  simpa only [div_eq_mul_inv, mul_comm] using h'

private theorem self_adjoint_sq {n : ℕ} {G X : Matrix (Fin n) (Fin n) K} {m α : K}
    (hGs : Gᵀ = G ∨ Gᵀ = -G)
    (hα : α ≠ 0) (hX : Xᵀ * G * X = m • G) (hX2 : X * X = α • 1) :
    G * X = ((m / α) ^ 2) • (G * X) := by
  have hXg := self_adjoint_eq hα hX hX2
  have htrans := congrArg Matrix.transpose hXg
  simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose] at htrans
  rcases hGs with hG | hG
  · rw [hG] at htrans
    rw [hXg] at htrans
    simpa [smul_smul, sq] using htrans
  · rw [hG] at htrans
    simp only [Matrix.neg_mul, Matrix.mul_neg, smul_neg, neg_inj] at htrans
    rw [hXg] at htrans
    simpa [smul_smul, sq] using htrans

private theorem alpha_fixed (h : UnitaryFieldData p f K) {n : ℕ} (hn : 0 < n)
    {X : Matrix (Fin n) (Fin n) K} {α : K} (hXr : X.map h.bar = X) (hX2 : X * X = α • 1) :
    h.bar α = α := by
  have hmap := congrArg (fun M => M.map h.bar) hX2
  simp only [Matrix.map_mul, hXr] at hmap
  rw [Matrix.map_smul' h.bar α 1 h.bar.map_mul] at hmap
  simp only [Matrix.map_one, map_zero, map_one] at hmap
  rw [hX2] at hmap
  have h00 := congrFun (congrFun hmap ⟨0, hn⟩) ⟨0, hn⟩
  simpa using h00.symm

private instance finite_fixedField (h : UnitaryFieldData p f K) : Finite h.fixedField :=
  haveI := h.finite
  Finite.of_injective (Subtype.val : h.fixedField → K) Subtype.val_injective

private theorem det_X_ne_zero {n : ℕ} (_hn : 0 < n) {X : Matrix (Fin n) (Fin n) K} {α : K}
    (hα : α ≠ 0) (hX2 : X * X = α • 1) : X.det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det hX2
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one,
    Fintype.card_fin] at h
  exact hα (pow_eq_zero_iff'.mp h.symm).1

private theorem self_adjoint_sq_eq_one {n : ℕ} (hn : 0 < n)
    {G X : Matrix (Fin n) (Fin n) K} {m α : K}
    (hG : IsUnit G.det) (hα : α ≠ 0) (hX : Xᵀ * G * X = m • G)
    (hX2 : X * X = α • 1) (hGs : Gᵀ = G ∨ Gᵀ = -G) :
    (m / α) ^ 2 = 1 := by
  have hsq := self_adjoint_sq hGs hα hX hX2
  have hGX : IsUnit (G * X).det := by
    rw [Matrix.det_mul]
    exact hG.mul (isUnit_iff_ne_zero.mpr (det_X_ne_zero hn hα hX2))
  have hcancel := congrArg (fun M => M * (G * X)⁻¹) hsq
  rw [Matrix.smul_mul, Matrix.mul_nonsing_inv _ hGX] at hcancel
  have h00 := congrFun (congrFun hcancel ⟨0, hn⟩) ⟨0, hn⟩
  simpa using h00.symm

private theorem self_adjoint_sign {n : ℕ} (hn : 0 < n)
    {G X : Matrix (Fin n) (Fin n) K} {m α : K}
    (hG : IsUnit G.det) (hα : α ≠ 0) (hX : Xᵀ * G * X = m • G)
    (hX2 : X * X = α • 1) (hGs : Gᵀ = G ∨ Gᵀ = -G) :
    Xᵀ * G = G * X ∨ Xᵀ * G = -(G * X) := by
  have hsq := self_adjoint_sq_eq_one hn hG hα hX hX2 hGs
  have hsign := sq_eq_one_iff.mp hsq
  have hXg := self_adjoint_eq hα hX hX2
  rcases hsign with h1 | hneg
  · left
    rw [hXg, h1, one_smul]
  · right
    rw [hXg, hneg, neg_one_smul]

private theorem map_realMat_bar (h : UnitaryFieldData p f K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) h.fixedField) :
    (M.map h.fixedField.subtype).map h.bar = M.map h.fixedField.subtype := by
  rw [Matrix.map_map]
  have hcomp : (h.bar : K → K) ∘ h.fixedField.subtype = h.fixedField.subtype := by
    ext x
    exact h.mem_fixedField.mp x.2
  rw [hcomp]

private theorem realMat_inv (h : UnitaryFieldData p f K) {n : ℕ}
    {M : Matrix (Fin n) (Fin n) h.fixedField} (hunit : IsUnit M.det) :
    (M.map h.fixedField.subtype)⁻¹ = (M⁻¹).map h.fixedField.subtype := by
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have h2 := congrArg (fun N => N.map h.fixedField.subtype) h1
  rw [Matrix.map_mul, Matrix.map_one h.fixedField.subtype (by simp) (by simp)] at h2
  exact Matrix.inv_eq_right_inv h2

private theorem hgne_map (h : UnitaryFieldData p f K) {n : ℕ}
    {g A : Matrix (Fin n) (Fin n) h.fixedField}
    (hg : ∀ d : h.fixedField, g * A * g⁻¹ ≠ d • A)
    (hgun : IsUnit g.det) (hA0 : A.map h.fixedField.subtype ≠ 0) :
    ∀ d : K, g.map h.fixedField.subtype * (A.map h.fixedField.subtype) *
      (g.map h.fixedField.subtype)⁻¹ ≠ d • (A.map h.fixedField.subtype) := by
  intro d hd
  have hgr : (g.map h.fixedField.subtype).map h.bar = g.map h.fixedField.subtype :=
    map_realMat_bar h g
  have hAr : (A.map h.fixedField.subtype).map h.bar = A.map h.fixedField.subtype :=
    map_realMat_bar h A
  have hginv : (g.map h.fixedField.subtype)⁻¹ = (g⁻¹).map h.fixedField.subtype :=
    realMat_inv h hgun
  have hginvr : ((g.map h.fixedField.subtype)⁻¹).map h.bar =
      (g.map h.fixedField.subtype)⁻¹ := by
    rw [hginv]
    exact map_realMat_bar h (g⁻¹)
  have hbar : h.bar d = d := by
    have hmap := congrArg (fun M => M.map h.bar) hd
    rw [Matrix.map_mul, Matrix.map_mul,
      Matrix.map_smul' h.bar d (A.map h.fixedField.subtype) h.bar.map_mul,
      hgr, hAr, hginvr] at hmap
    have hsub : (h.bar d - d) • (A.map h.fixedField.subtype) = 0 := by
      rw [sub_smul, ← hmap, hd, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hA0)
  let dk : h.fixedField := ⟨d, h.mem_fixedField.mpr hbar⟩
  have hd' : g * A * g⁻¹ = dk • A := by
    apply Matrix.map_injective h.fixedField.subtype_injective
    have hleft : (g * A * g⁻¹).map h.fixedField.subtype =
        g.map h.fixedField.subtype * (A.map h.fixedField.subtype) *
          (g.map h.fixedField.subtype)⁻¹ := by
      rw [Matrix.map_mul, Matrix.map_mul, ← hginv]
    have hright : (dk • A).map h.fixedField.subtype =
        d • (A.map h.fixedField.subtype) := by
      rw [Matrix.map_smul' h.fixedField.subtype dk A (by simp)]
      rfl
    change (g * A * g⁻¹).map h.fixedField.subtype =
      (dk • A).map h.fixedField.subtype
    rw [hleft, hright]
    exact hd
  exact hg dk hd'

private theorem orth_conj_g_case (h : UnitaryFieldData p f K) {n : ℕ}
    {G X A : Matrix (Fin n) (Fin n) K} {g : Matrix (Fin n) (Fin n) K}
    (hgr : g.map h.bar = g) (hgΦ : gᵀ * G * g = G) (hg1 : g.det = 1)
    (hgc : g * A * g⁻¹ * A = A * (g * A * g⁻¹))
    (hgne : ∀ d : K, g * A * g⁻¹ ≠ d • A)
    {c : K} (hc : c ≠ 0) (hA : A = c • X) :
    ∃ g X' : Matrix (Fin n) (Fin n) K, g.map h.bar = g ∧ gᵀ * G * g = G ∧
      g.det = 1 ∧ g * X = X' * g ∧ X * X' = X' * X ∧ ∀ d : K, X' ≠ d • X := by
  let X' := g * X * g⁻¹
  have hgX : g * X = X' * g := by
    rw [show X' = g * X * g⁻¹ from rfl, Matrix.mul_assoc, Matrix.mul_assoc]
    have hg_inv : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ (by rw [hg1]; exact isUnit_one)
    rw [hg_inv, Matrix.mul_one]
  have hcomm : X * X' = X' * X := by
    rw [hA] at hgc
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] at hgc
    have hcc : c * c ≠ 0 := mul_ne_zero hc hc
    have hcancel := congrArg (fun M => (c * c)⁻¹ • M) hgc
    simp only [smul_smul, inv_mul_cancel₀ hcc, one_smul] at hcancel
    rw [show X' = g * X * g⁻¹ from rfl]
    exact hcancel.symm
  have hX'ne : ∀ d : K, X' ≠ d • X := by
    intro d hd
    have hdA : g * A * g⁻¹ = d • A := by
      rw [hA]
      rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      rw [show g * X * g⁻¹ = d • X from hd]
      rw [smul_smul c d X, mul_comm c d]
    exact hgne d hdA
  exact ⟨g, X', hgr, hgΦ, hg1, hgX, hcomm, hX'ne⟩

private theorem orth_conj_Y_case (h : UnitaryFieldData p f K) {n : ℕ}
    {G X A : Matrix (Fin n) (Fin n) K} {Y : Matrix (Fin n) (Fin n) h.fixedField}
    (hgr : G.map h.bar = G) (hXunit : IsUnit X.det)
    (hY1 : Y ≠ 1) (hY3 : (Y - 1) ^ 3 = 0)
    (hYΦ : Yᵀ * realMat h G hgr * Y = realMat h G hgr)
    {c : K} (hA : A = c • X) (hc : c ≠ 0)
    (hAY : A * Y.map h.fixedField.subtype * A⁻¹ = (Y.map h.fixedField.subtype)⁻¹) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, gramForm h G x y = 0) ∧
      (∀ w ∈ W, X *ᵥ w ∈ W) ∧ ∀ w ∈ W, (fun i => h.bar (w i)) ∈ W := by
  let YK : Matrix (Fin n) (Fin n) K := Y.map h.fixedField.subtype
  have hYKr : YK.map h.bar = YK := map_realMat_bar h Y
  have hYK1 : YK ≠ 1 := by
    intro h1
    have h2 : Y.map h.fixedField.subtype = (1 : Matrix (Fin n) (Fin n) h.fixedField).map
        h.fixedField.subtype := by simpa [YK] using h1
    have h3 : Y = 1 := Matrix.map_injective h.fixedField.subtype_injective h2
    exact hY1 h3
  have hYK3 : (YK - 1) ^ 3 = 0 := by
    have h3 : (Y - 1) * (Y - 1) * (Y - 1) = 0 := by
      simpa [pow_succ, pow_two] using hY3
    have h4 := congrArg (fun M => M.map h.fixedField.subtype) h3
    simp only [Matrix.map_mul, Matrix.map_sub h.fixedField.subtype (by simp),
      Matrix.map_one h.fixedField.subtype (by simp) (by simp)] at h4
    simpa [YK, pow_succ, pow_two] using h4
  have hYKΦ : YKᵀ * G * YK = G := by
    have h4 := congrArg (fun M => M.map h.fixedField.subtype) hYΦ
    simp only [Matrix.map_mul, Matrix.transpose_map, realMat_map h hgr] at h4
    simpa [YK] using h4
  have hXY : X * YK * X⁻¹ = YK⁻¹ := by
    rw [hA] at hAY
    have hcX_inv : (c • X)⁻¹ = c⁻¹ • X⁻¹ := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hXunit, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
    rw [hcX_inv] at hAY
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul] at hAY
    exact hAY
  exact exists_stable_isotropic_of_inverted_unipotent h hYKr hYK1 hYK3 hYKΦ hXunit hXY

theorem real_stable_or_orth_conj (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hn : 3 ≤ n)
    {G X : Matrix (Fin n) (Fin n) K} (hGr : G.map h.bar = G) (hXr : X.map h.bar = X)
    (hG : IsUnit G.det) (hGs : Gᵀ = G ∨ Gᵀ = -G) {m α : K} (hα : α ≠ 0)
    (hX : Xᵀ * G * X = m • G) (hX2 : X * X = α • 1) (hXs : ∀ c : K, X ≠ c • 1) :
    (∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, gramForm h G x y = 0) ∧
      (∀ w ∈ W, X *ᵥ w ∈ W) ∧ ∀ w ∈ W, (fun i => h.bar (w i)) ∈ W) ∨
    (Gᵀ = G ∧ Xᵀ * G = G * X ∧ ∃ g X' : Matrix (Fin n) (Fin n) K, g.map h.bar = g ∧
      gᵀ * G * g = G ∧ g.det = 1 ∧ g * X = X' * g ∧ X * X' = X' * X ∧ ∀ c : K, X' ≠ c • X) := by
  have hn0 : 0 < n := by omega
  have hsign := self_adjoint_sign hn0 hG hα hX hX2 hGs
  rcases hGs with hGsymm | hGskew
  · rcases hsign with hXG | hXG_neg
    · let k := h.fixedField
      let ι := h.fixedField.subtype
      let Gk := realMat h G hGr
      let Xk := realMat h X hXr
      have hGk_map : Gk.map ι = G := realMat_map h hGr
      have hXk_map : Xk.map ι = X := realMat_map h hXr
      have hGk_det : IsUnit Gk.det := realMat_isUnit_det h hGr hG
      have hk : ringChar k ≠ 2 :=
        CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow.ringChar_fixedField_ne_two
          h hp
      have hGk_symm : Gkᵀ = Gk := by
        apply Matrix.map_injective h.fixedField.subtype_injective
        change Gkᵀ.map ι = Gk.map ι
        rw [Matrix.transpose_map, realMat_map h hGr]
        exact hGsymm
      have hXGk : Xkᵀ * Gk = Gk * Xk := by
        apply Matrix.map_injective h.fixedField.subtype_injective
        change (Xkᵀ * Gk).map ι = (Gk * Xk).map ι
        rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
        rw [realMat_map h hXr, realMat_map h hGr]
        exact hXG
      have hαk_fixed : h.bar α = α := alpha_fixed h hn0 hXr hX2
      let αk : k := ⟨α, h.mem_fixedField.mpr hαk_fixed⟩
      have hαk_ne_zero : αk ≠ 0 := by
        intro h0
        have h1 : α = 0 := congrArg Subtype.val h0
        exact hα h1
      have hXk_sq : Xk * Xk = αk • 1 := by
        apply Matrix.map_injective h.fixedField.subtype_injective
        change (Xk * Xk).map ι = (αk • (1 : Matrix (Fin n) (Fin n) k)).map ι
        rw [Matrix.map_mul, Matrix.map_smul' h.fixedField.subtype αk 1 (by simp)]
        rw [Matrix.map_one h.fixedField.subtype (by simp) (by simp)]
        rw [realMat_map h hXr]
        have hαk_val : ι αk = α := rfl
        rw [hαk_val]
        exact hX2
      have hXk_nonscalar : ∀ c : k, Xk ≠ c • 1 := by
        intro c hc
        apply hXs (c : K)
        have hmap := congrArg (fun M => M.map ι) hc
        rw [Matrix.map_smul' h.fixedField.subtype c
          (1 : Matrix (Fin n) (Fin n) k) (by simp)] at hmap
        rw [Matrix.map_one h.fixedField.subtype (by simp) (by simp)] at hmap
        simpa [hXk_map] using hmap
      by_cases hsq : IsSquare αk
      · obtain ⟨s, hs⟩ := hsq
        have hs_ne_zero : s ≠ 0 := by
          intro hs0
          apply hαk_ne_zero
          rw [hs, hs0, mul_zero]
        let A := s⁻¹ • Xk
        have hA_sq : A * A = 1 := by
          simp only [A, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          rw [hXk_sq, hs, smul_smul]
          have hcoef : s⁻¹ * s⁻¹ * (s * s) = 1 := by
            field_simp [hs_ne_zero]
          rw [hcoef, one_smul]
        have hAΦ : Aᵀ * Gk = Gk * A := by
          simp only [A, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
          rw [hXGk]
        have hA_nonscalar : ∀ c : k, A ≠ c • 1 := by
          intro c hc
          have hXk_scalar : Xk = (s * c) • 1 := by
            have h := congrArg (fun M => s • M) hc
            simp only [A, smul_smul] at h
            rwa [mul_inv_cancel₀ hs_ne_zero, one_smul] at h
          exact hXk_nonscalar (s * c) hXk_scalar
        have hsK_ne_zero : (s : K) ≠ 0 := by
          intro h0
          apply hs_ne_zero
          exact Subtype.coe_injective h0
        rcases PSLOuter.orth_conj_or_inverted_unipotent_of_sq hk hn hGk_det hGk_symm
          hA_sq hA_nonscalar hAΦ with hg | hY
        · right
          refine ⟨hGsymm, hXG, ?_⟩
          obtain ⟨g, hgΦ, hg1, hgc, hgne⟩ := hg
          let gK := g.map ι
          have hgrK : gK.map h.bar = gK := map_realMat_bar h g
          have hgΦK : gKᵀ * G * gK = G := by
            have hmap := congrArg (fun M => M.map ι) hgΦ
            simp only [Matrix.map_mul, Matrix.transpose_map, hGk_map] at hmap
            simpa [gK] using hmap
          have hg1K : gK.det = 1 := by
            have hmap := RingHom.map_det ι g
            rw [RingHom.mapMatrix_apply] at hmap
            rw [hg1, map_one] at hmap
            simpa [gK] using hmap.symm
          have hgcK : gK * (A.map ι) * gK⁻¹ * (A.map ι) = (A.map ι) * (gK * (A.map ι) * gK⁻¹) := by
            have hmap := congrArg (fun M => M.map ι) hgc
            simp only [Matrix.map_mul] at hmap
            rw [← realMat_inv h (by rw [hg1]; exact isUnit_one)] at hmap
            simpa [gK, ι] using hmap
          have hgneK : ∀ d : K, gK * (A.map ι) * gK⁻¹ ≠ d • (A.map ι) := by
            have hA0 : A.map ι ≠ 0 := by
              intro hzero
              have hsq : (A.map ι) * (A.map ι) = 1 := by
                have hmap := congrArg (fun M => M.map ι) hA_sq
                rw [Matrix.map_mul] at hmap
                have hone : (1 : Matrix (Fin n) (Fin n) k).map ι = 1 := by
                  ext i j
                  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
                rw [hone] at hmap
                exact hmap
              rw [hzero, mul_zero] at hsq
              have h00 := congrFun (congrFun hsq ⟨0, hn0⟩) ⟨0, hn0⟩
              exact zero_ne_one h00
            simpa [gK, ι] using
              hgne_map h hgne (by rw [hg1]; exact isUnit_one) hA0
          have hA_map : A.map ι = s⁻¹ • X := by
            rw [show A = s⁻¹ • Xk from rfl]
            rw [Matrix.map_smul' h.fixedField.subtype s⁻¹ Xk (by simp)]
            rw [realMat_map h hXr]
            rfl
          obtain ⟨g', X', hgr', hgΦ', hg1', hgX', hcomm', hX'ne'⟩ :=
            orth_conj_g_case h hgrK hgΦK hg1K hgcK hgneK (inv_ne_zero hsK_ne_zero) hA_map
          exact ⟨g', X', hgr', hgΦ', hg1', hgX', hcomm', hX'ne'⟩
        · left
          obtain ⟨Y, hY1, hY3, hYΦ, hAY⟩ := hY
          have hXunit : IsUnit X.det := by
            rw [isUnit_iff_ne_zero]
            exact det_X_ne_zero hn0 hα hX2
          have hA_map : A.map ι = s⁻¹ • X := by
            rw [show A = s⁻¹ • Xk from rfl]
            rw [Matrix.map_smul' h.fixedField.subtype s⁻¹ Xk (by simp)]
            rw [realMat_map h hXr]
            rfl
          have hAunit : IsUnit A.det := by
            rw [isUnit_iff_ne_zero]
            intro h0
            have h := congrArg Matrix.det hA_sq
            rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h
            exact zero_ne_one h
          have hY_unit : IsUnit Y.det := by
            rw [isUnit_iff_ne_zero]
            intro h0
            have hdet := congrArg Matrix.det hYΦ
            rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at hdet
            exact hGk_det.ne_zero hdet.symm
          have hAYK : (A.map ι) * Y.map ι * (A.map ι)⁻¹ = (Y.map ι)⁻¹ := by
            have hmap := congrArg (fun M => M.map ι) hAY
            rw [Matrix.map_mul, Matrix.map_mul] at hmap
            rw [← realMat_inv h hAunit, ← realMat_inv h hY_unit] at hmap
            exact hmap
          exact orth_conj_Y_case h hGr hXunit hY1 hY3 hYΦ hA_map (inv_ne_zero hsK_ne_zero) hAYK
      · rcases PSLOuter.orth_conj_or_inverted_unipotent_of_not_sq hk hn hGk_det hGk_symm
          hXk_sq hsq hXGk with hg | hY
        · right
          refine ⟨hGsymm, hXG, ?_⟩
          obtain ⟨g, hgΦ, hg1, hgc, hgne⟩ := hg
          let gK := g.map ι
          have hgrK : gK.map h.bar = gK := map_realMat_bar h g
          have hgΦK : gKᵀ * G * gK = G := by
            have hmap := congrArg (fun M => M.map ι) hgΦ
            simp only [Matrix.map_mul, Matrix.transpose_map, hGk_map] at hmap
            simpa [gK] using hmap
          have hg1K : gK.det = 1 := by
            have hmap := RingHom.map_det ι g
            rw [RingHom.mapMatrix_apply] at hmap
            rw [hg1, map_one] at hmap
            simpa [gK] using hmap.symm
          have hgcK : gK * (Xk.map ι) * gK⁻¹ * (Xk.map ι) =
              (Xk.map ι) * (gK * (Xk.map ι) * gK⁻¹) := by
            have hmap := congrArg (fun M => M.map ι) hgc
            simp only [Matrix.map_mul] at hmap
            rw [← realMat_inv h (by rw [hg1]; exact isUnit_one)] at hmap
            simpa [gK, ι] using hmap
          have hXunit : IsUnit X.det := by
            rw [isUnit_iff_ne_zero]
            exact det_X_ne_zero hn0 hα hX2
          have hgneK : ∀ d : K, gK * (Xk.map ι) * gK⁻¹ ≠ d • (Xk.map ι) := by
            have hX0 : Xk.map ι ≠ 0 := by
              rw [hXk_map]
              intro hzero
              have hdet : X.det = 0 := by
                have hne : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
                rw [hzero]
                exact @Matrix.det_zero (Fin n) _ _ K _ hne
              exact (isUnit_iff_ne_zero.mp hXunit) hdet
            simpa [gK, ι] using
              hgne_map h hgne (by rw [hg1]; exact isUnit_one) hX0
          have hA_map : Xk.map ι = (1 : K) • X := by
            rw [one_smul]
            exact hXk_map
          obtain ⟨g', X', hgr', hgΦ', hg1', hgX', hcomm', hX'ne'⟩ :=
            orth_conj_g_case h hgrK hgΦK hg1K hgcK hgneK one_ne_zero hA_map
          exact ⟨g', X', hgr', hgΦ', hg1', hgX', hcomm', hX'ne'⟩
        · left
          obtain ⟨Y, hY1, hY3, hYΦ, hAY⟩ := hY
          have hXunit : IsUnit X.det := by
            rw [isUnit_iff_ne_zero]
            exact det_X_ne_zero hn0 hα hX2
          have hXk_unit : IsUnit Xk.det := realMat_isUnit_det h hXr hXunit
          have hY_unit : IsUnit Y.det := by
            rw [isUnit_iff_ne_zero]
            intro h0
            have hdet := congrArg Matrix.det hYΦ
            rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, mul_zero] at hdet
            exact hGk_det.ne_zero hdet.symm
          have hAYK : Xk.map ι * Y.map ι * (Xk.map ι)⁻¹ = (Y.map ι)⁻¹ := by
            have hmap := congrArg (fun M => M.map ι) hAY
            rw [Matrix.map_mul, Matrix.map_mul] at hmap
            rw [realMat_inv h hXk_unit, realMat_inv h hY_unit]
            exact hmap
          exact orth_conj_Y_case h hGr hXunit hY1 hY3 hYΦ
            (by rw [one_smul]; exact hXk_map) one_ne_zero hAYK
    · left
      exact exists_real_isotropic_stable_of_skew h hp hn hGr hXr hX hX2 (Or.inr ⟨hGsymm, hXG_neg⟩)
  · left
    exact exists_real_isotropic_stable_of_skew h hp hn hGr hXr hX hX2 (Or.inl hGskew)

end CFSG.LocalAnalysis.WeakClosure81.UOuter
