module

public import CFSG.LocalAnalysis.StandardType.GGL45TGSU
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGCoverRkFieldFix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix
open CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private theorem scalar_mul_eq_smul_mat {d : ℕ} {K : Type} [Field K] (c : K)
    (M : Matrix (Fin d) (Fin d) K) : Matrix.scalar (Fin d) c * M = c • M := by
  ext i j
  rw [Matrix.scalar_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem gl_scalar_mul {d : ℕ} {K : Type} [Field K] (a b : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin d) a * Matrix.GeneralLinearGroup.scalar (Fin d) b =
      Matrix.GeneralLinearGroup.scalar (Fin d) (a * b) := by
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  rw [Matrix.scalar_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  · intro b' _ hb; simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem gl_scalar_one {d : ℕ} {K : Type} [Field K] :
    Matrix.GeneralLinearGroup.scalar (Fin d) (1 : Kˣ) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hij]

private theorem herm_scalar_mul {n d : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    (c : K) (M : Matrix (Fin d) (Fin d) K) :
    ((Matrix.scalar (Fin d) c * M).map h.bar)ᵀ * (Matrix.scalar (Fin d) c * M) =
      (h.bar c * c) • ((M.map h.bar)ᵀ * M) := by
  rw [scalar_mul_eq_smul_mat]
  rw [show (c • M).map h.bar = h.bar c • M.map h.bar from by ext i j; simp,
    Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem unitary_mul_mat {n d : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    {A B : Matrix (Fin d) (Fin d) K}
    (hA : (A.map h.bar)ᵀ * A = 1) (hB : (B.map h.bar)ᵀ * B = 1) :
    ((A * B).map h.bar)ᵀ * (A * B) = 1 := by
  rw [← Matrix.mul_one ((A * B).map h.bar)ᵀ, conjTranspose_mul_mul h 1 A B]
  simp only [Matrix.mul_one, Matrix.one_mul, hA, hB]

private theorem unitary_inv_gl {n d : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    {A : GL (Fin d) K} (hA : ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      (A : Matrix (Fin d) (Fin d) K) = 1) :
    (((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
  have hAA : (A : Matrix (Fin d) (Fin d) K) *
      ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj := conjTranspose_mul_mul h 1 (A : Matrix (Fin d) (Fin d) K)
    ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
  rw [hAA] at hconj
  simp only [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one,
    Matrix.one_mul, Matrix.mul_one, hA] at hconj
  exact hconj.symm

private theorem cu_normalizes_unitarySU {n d : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) {x : GL (Fin d) K} (hx : x ∈ GGL45TG.SU.CU h d)
    {g : GL (Fin d) K} (hg : g ∈ unitarySU 2 n K d) :
    x * g * x⁻¹ ∈ unitarySU 2 n K d := by
  have hg' : g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
    rw [GGL45TG.SU.mem_su_iff h]
    exact ⟨(mem_unitarySU_iff h).mp hg |>.2, (mem_unitarySU_iff h).mp hg |>.1⟩
  have hres := GGL45TG.SU.conj_mem_su h hx hg'
  rw [GGL45TG.SU.mem_su_iff h] at hres
  rw [mem_unitarySU_iff h]
  exact ⟨hres.2, hres.1⟩

private theorem map_mem_unitarySU {n d : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (σ : K ≃+* K) {g : GL (Fin d) K}
    (hg : g ∈ unitarySU 2 n K d) :
    Matrix.GeneralLinearGroup.map σ.toRingHom g ∈ unitarySU 2 n K d := by
  have hg' : g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n) := by
    rw [GGL45TG.SU.mem_su_iff h]
    exact ⟨(mem_unitarySU_iff h).mp hg |>.2, (mem_unitarySU_iff h).mp hg |>.1⟩
  have hres := GGL45TG.SU.map_mem_su h σ hg'
  rw [GGL45TG.SU.mem_su_iff h] at hres
  rw [mem_unitarySU_iff h]
  exact ⟨hres.2, hres.1⟩

private theorem exists_decomp_cu {n d : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hd : 1 ≤ d) {g : GL (Fin d) K}
    (hg : g ∈ GGL45TG.SU.CU h d) :
    ∃ (s₀ : ↥(unitarySU 2 n K d)) (D' : GL (Fin d) K) (v : Fin d → K),
      (D' : Matrix (Fin d) (Fin d) K) = diagonal v ∧
      D' ∈ GGL45TG.SU.CU h d ∧ g = (s₀ : GL (Fin d) K) * D' := by
  classical
  obtain ⟨μ, hμ⟩ := hg
  have hμfix : h.bar μ = μ := by
    have e1 : (((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
        (g : Matrix (Fin d) (Fin d) K)) ⟨0, hd⟩ ⟨0, hd⟩ = μ := by
      rw [hμ]; simp
    rw [← e1]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
      UnitaryFieldData.bar_bar]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hdetg : (g : Matrix (Fin d) (Fin d) K).det ≠ 0 := by
    intro h0
    have hunit : IsUnit ((g : Matrix (Fin d) (Fin d) K).det) :=
      (g.isUnit).map (Matrix.detMonoidHom (n := Fin d) (R := K))
    rw [h0] at hunit
    exact not_isUnit_zero hunit
  have hdetbar : ((g : Matrix (Fin d) (Fin d) K).map h.bar).det =
      h.bar ((g : Matrix (Fin d) (Fin d) K).det) := by
    have h1 := RingHom.map_det h.bar (g : Matrix (Fin d) (Fin d) K)
    rw [show h.bar.mapMatrix (g : Matrix (Fin d) (Fin d) K) =
      ((g : Matrix (Fin d) (Fin d) K).map h.bar) from rfl] at h1
    exact h1.symm
  have hdetbar_ne : ((g : Matrix (Fin d) (Fin d) K).map h.bar).det ≠ 0 := by
    rw [hdetbar]
    intro h0
    exact hdetg ((h.bar_eq_zero_iff).mp h0)
  have hL : (((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      (g : Matrix (Fin d) (Fin d) K)).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hdetbar_ne hdetg
  have hdet_eq : (((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      (g : Matrix (Fin d) (Fin d) K)).det = μ ^ d := by
    have h1 := congrArg Matrix.det hμ
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at h1
    simpa [Matrix.det_mul, Matrix.det_transpose] using h1
  have hμ0 : μ ≠ 0 := by
    intro h0
    have : (((g : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
        (g : Matrix (Fin d) (Fin d) K)).det = 0 := by
      rw [hdet_eq, h0, zero_pow (by omega : d ≠ 0)]
    exact hL this
  obtain ⟨lam, hlam⟩ := h.normHom_surjective ⟨μ, h.mem_fixedField.mpr hμfix⟩
  have hlam_norm : h.norm lam = μ := by
    have := congrArg (fun x : h.fixedField => (x : K)) hlam
    simpa using this
  have hlam_ne : lam ≠ 0 := by
    intro h0
    have : h.norm lam = 0 := by simp [UnitaryFieldData.norm, h0]
    rw [hlam_norm] at this
    exact hμ0 this
  have hbar_lam_mul : h.bar lam * lam = μ := by
    rw [mul_comm, ← hlam_norm]; rfl
  set z : Kˣ := Units.mk0 lam hlam_ne with hz
  set g' : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) z⁻¹ * g with hg'def
  have hg'val : (g' : Matrix (Fin d) (Fin d) K) =
      Matrix.scalar (Fin d) ((z⁻¹ : Kˣ) : K) * (g : Matrix (Fin d) (Fin d) K) := by
    rw [hg'def, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  have hg'herm : ((g' : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      (g' : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hg'val, herm_scalar_mul h, hμ]
    have hc : h.bar ((z⁻¹ : Kˣ) : K) * ((z⁻¹ : Kˣ) : K) = μ⁻¹ := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hz]
      simp only [Units.val_mk0]
      rw [← mul_inv, hbar_lam_mul]
    rw [hc, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  set δ : K := (g' : Matrix (Fin d) (Fin d) K).det with hδ
  have hδ_ne : δ ≠ 0 := by
    intro h0
    have hunit : IsUnit ((g' : Matrix (Fin d) (Fin d) K).det) :=
      (g'.isUnit).map (Matrix.detMonoidHom (n := Fin d) (R := K))
    rw [← hδ] at hunit
    rw [h0] at hunit
    exact not_isUnit_zero hunit
  have hdetbar' : ((g' : Matrix (Fin d) (Fin d) K).map h.bar).det = h.bar δ := by
    have h1 := RingHom.map_det h.bar (g' : Matrix (Fin d) (Fin d) K)
    rw [show h.bar.mapMatrix (g' : Matrix (Fin d) (Fin d) K) =
      ((g' : Matrix (Fin d) (Fin d) K).map h.bar) from rfl] at h1
    rw [hδ]
    exact h1.symm
  have hδnorm : h.bar δ * δ = 1 := by
    have := congrArg Matrix.det hg'herm
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, hdetbar'] at this
    exact this
  set iP : Fin d := ⟨0, hd⟩ with hiP
  set e' : Fin d → K := fun l => if l = iP then δ else 1 with he'
  have hdetD1 : (Matrix.diagonal e').det = δ := by
    rw [Matrix.det_diagonal]
    rw [Finset.prod_eq_single iP]
    · simp [he']
    · intro b _ hb; simp [he', hb]
    · intro h; exact absurd (Finset.mem_univ iP) h
  set D₁ : GL (Fin d) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal e')
      (by rw [hdetD1]; exact hδ_ne) with hD1def
  have hD1val : (D₁ : Matrix (Fin d) (Fin d) K) = Matrix.diagonal e' :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hD1herm : ((D₁ : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      (D₁ : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hD1val, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = iP
    · subst hi; simp [he', hδnorm]
    · simp [he', hi]
  have hD1cu : D₁ ∈ GGL45TG.SU.CU h d := by
    rw [GGL45TG.SU.mem_cu_iff]
    exact ⟨1, by rw [hD1herm, one_smul]⟩
  have hs0mem : g' * D₁⁻¹ ∈ unitarySU 2 n K d := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · have hD1det : Matrix.GeneralLinearGroup.det D₁ = Units.mk0 δ hδ_ne := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply, hD1val, hdetD1, Units.val_mk0]
      have hdetg' : Matrix.GeneralLinearGroup.det g' = Units.mk0 δ hδ_ne := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        exact hδ.symm
      have h1 : Matrix.GeneralLinearGroup.det (g' * D₁⁻¹) = 1 := by
        rw [map_mul, map_inv, hdetg', hD1det, mul_inv_cancel]
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      rw [h1, Units.val_one]
    · exact unitary_mul_mat h hg'herm (unitary_inv_gl h hD1herm)
  refine ⟨⟨g' * D₁⁻¹, hs0mem⟩, Matrix.GeneralLinearGroup.scalar (Fin d) z * D₁,
    fun i => (z : K) * e' i, ?_, ?_, ?_⟩
  ·
    show ((Matrix.GeneralLinearGroup.scalar (Fin d) z * D₁ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) = diagonal (fun i => (z : K) * e' i)
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hD1val, scalar_mul_eq_smul_mat,
      ← Matrix.diagonal_smul]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  ·
    exact (GGL45TG.SU.CU h d).mul_mem (GGL45TG.SU.scalar_mem_cu h z) hD1cu
  ·
    show g = (g' * D₁⁻¹ : GL (Fin d) K) * (Matrix.GeneralLinearGroup.scalar (Fin d) z * D₁)
    have hcentz : ∀ M : GL (Fin d) K,
        M * Matrix.GeneralLinearGroup.scalar (Fin d) z =
          Matrix.GeneralLinearGroup.scalar (Fin d) z * M :=
      fun M => Subgroup.mem_center_iff.mp (TableB.scalar_mem_center z) M
    have hsc : Matrix.GeneralLinearGroup.scalar (Fin d) z *
        Matrix.GeneralLinearGroup.scalar (Fin d) z⁻¹ = 1 := by
      rw [gl_scalar_mul, mul_inv_cancel, gl_scalar_one]
    have hg_eq' : g = Matrix.GeneralLinearGroup.scalar (Fin d) z * g' := by
      rw [hg'def, ← mul_assoc, hsc, one_mul]
    rw [hg_eq']
    have hD : D₁⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin d) z * D₁) =
        Matrix.GeneralLinearGroup.scalar (Fin d) z := by
      rw [← mul_assoc, hcentz D₁⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [show (g' * D₁⁻¹ : GL (Fin d) K) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) z * D₁) =
        g' * (D₁⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin d) z * D₁)) by rw [mul_assoc],
      hD]
    exact (hcentz g').symm

private theorem ratio_fixed {n d p m : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (h : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c))
    {σ : K ≃+* K} (hp : p.Prime) (hσ : σ ^ p ^ m = 1)
    {e : MulAut L'} (hep : e ^ p = 1) {t : Fin d → K} (ht : ActsDiagU φ e t) :
    ∃ μ' : K, μ' ≠ 0 ∧ ∀ i, σ (t i) = μ' * t i := by
  set i0 : Fin d := ⟨0, by omega⟩ with hi0
  have hfix : ∀ i j, σ (t i * (t j)⁻¹) = t i * (t j)⁻¹ := fun i j =>
    fieldAut_fixes_pow_eq_one hp hσ (ActsDiagU.ratio_pow h hd hφker ht hep i j)
  have hσne : σ (t i0) ≠ 0 := by
    intro h0
    exact (ht.ne_zero i0) (σ.injective (by rw [h0, map_zero]))
  refine ⟨σ (t i0) * (t i0)⁻¹, ?_, ?_⟩
  · exact mul_ne_zero hσne (inv_ne_zero (ht.ne_zero i0))
  · intro i
    have hh := hfix i i0
    rw [map_mul, map_inv₀] at hh
    have h2 : σ (t i) = t i * (t i0)⁻¹ * σ (t i0) := by
      have h3 := congrArg (fun x => x * σ (t i0)) hh
      rw [mul_assoc] at h3
      rwa [inv_mul_cancel₀ hσne, mul_one] at h3
    rw [h2]
    ring

private theorem eq_of_on_su {n d : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hsurj : Function.Surjective φ)
    {f g : MulAut L'} (h : ∀ x : ↥(unitarySU 2 n K d), f (φ x) = g (φ x)) : f = g := by
  ext r
  obtain ⟨x, rfl⟩ := hsurj r
  exact h x

theorem exists_rho_commute_diag {d n p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hd : 3 ≤ d)
    {φ : ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    (hM : UnitTB.Model φ) {σ : K ≃+* K} {m : ℕ} (hσ : σ ^ p ^ m = 1) {g : GL (Fin d) K}
    (hg : g ∈ GGL45TG.SU.CU hM.field d)
    {a : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (ha : ∀ x y : ↥(unitarySU 2 n K d),
      (y : GL (Fin d) K) = g * Matrix.GeneralLinearGroup.map σ.toRingHom x * g⁻¹ →
        a (φ x) = φ y) :
    ∃ ρ : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      ∀ e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))), e ^ p = 1 →
        (∃ t : Fin d → K, ActsDiagU φ e t) → Commute ((MulAut.conj ρ)⁻¹ * a) e := by
  obtain ⟨s₀, D', v, hD'mat, hD'cu, hg_eq⟩ := exists_decomp_cu hM.field (by omega) hg
  refine ⟨φ s₀, fun e hep ht => ?_⟩
  obtain ⟨t, ht⟩ := ht
  obtain ⟨μ', hμ'ne, hμ't⟩ := ratio_fixed hM.field hd hM.ker hp hσ hep ht
  obtain ⟨E, hE, hEmat, hactE⟩ := ht
  have hmem : ∀ y : ↥(unitarySU 2 n K d),
      D' * Matrix.GeneralLinearGroup.map σ.toRingHom y * D'⁻¹ ∈ unitarySU 2 n K d :=
    fun y => cu_normalizes_unitarySU hM.field hD'cu (map_mem_unitarySU hM.field σ y.2)
  have hconj : (MulAut.conj (φ s₀))⁻¹ = MulAut.conj ((φ s₀)⁻¹) := by
    ext z; simp [MulAut.conj_apply]
  have hA : ∀ y : ↥(unitarySU 2 n K d),
      (MulAut.conj (φ s₀))⁻¹ (a (φ y)) =
        φ ⟨D' * Matrix.GeneralLinearGroup.map σ.toRingHom y * D'⁻¹, hmem y⟩ := by
    intro y
    have hy_mem : g * Matrix.GeneralLinearGroup.map σ.toRingHom y * g⁻¹ ∈ unitarySU 2 n K d :=
      cu_normalizes_unitarySU hM.field hg (map_mem_unitarySU hM.field σ y.2)
    have hya : a (φ y) = φ (⟨g * Matrix.GeneralLinearGroup.map σ.toRingHom y * g⁻¹, hy_mem⟩ :
        ↥(unitarySU 2 n K d)) := ha y _ rfl
    rw [hya, hconj, MulAut.conj_apply, inv_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (s₀ : GL (Fin d) K)⁻¹ *
        (g * Matrix.GeneralLinearGroup.map σ.toRingHom y * g⁻¹) * (s₀ : GL (Fin d) K) =
      D' * Matrix.GeneralLinearGroup.map σ.toRingHom y * D'⁻¹
    rw [hg_eq, _root_.mul_inv_rev]
    group
  apply eq_of_on_su hM.surj
  intro x
  have hcx : (conjN E hE x : GL (Fin d) K) = E * x * E⁻¹ := coe_conjN E hE x
  set s : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 μ' hμ'ne)
    with hsdef
  have hcent : ∀ N : GL (Fin d) K, s * N = N * s :=
    fun N => (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (Units.mk0 μ' hμ'ne)) N).symm
  have hcenti : ∀ N : GL (Fin d) K, s⁻¹ * N = N * s⁻¹ :=
    fun N => (Subgroup.mem_center_iff.mp
      (Subgroup.inv_mem _ (TableB.scalar_mem_center (Units.mk0 μ' hμ'ne))) N).symm
  have hσE : Matrix.GeneralLinearGroup.map σ.toRingHom E = s * E := by
    rw [hsdef]
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar,
      show (↑(Matrix.GeneralLinearGroup.map σ.toRingHom E) : Matrix (Fin d) (Fin d) K) =
        (E : Matrix (Fin d) (Fin d) K).map σ from rfl,
      hEmat, Matrix.diagonal_map (map_zero σ), scalar_mul_eq_smul_mat, ← Matrix.diagonal_smul]
    congr 1
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [hμ't i, Units.val_mk0]
  have hD'E : D' * E = E * D' := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD'mat, hEmat, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm (v i) (t i)
  have hD'Ei : E⁻¹ * D'⁻¹ = D'⁻¹ * E⁻¹ := by
    rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hD'E]
  set Mx : GL (Fin d) K := Matrix.GeneralLinearGroup.map σ.toRingHom x with hMxdef
  have hconjE : Matrix.GeneralLinearGroup.map σ.toRingHom E * Mx *
        (Matrix.GeneralLinearGroup.map σ.toRingHom E)⁻¹ = E * Mx * E⁻¹ := by
    rw [hσE, _root_.mul_inv_rev]
    calc (s * E) * Mx * (E⁻¹ * s⁻¹)
        = E * (s * Mx) * (E⁻¹ * s⁻¹) := by rw [hcent E]; group
      _ = E * (Mx * s) * (E⁻¹ * s⁻¹) := by rw [hcent Mx]
      _ = E * Mx * E⁻¹ := by
            rw [show E * (Mx * s) * (E⁻¹ * s⁻¹) = E * Mx * (s * E⁻¹) * s⁻¹ by group,
              hcent E⁻¹]
            group
  have hkey : D' * Matrix.GeneralLinearGroup.map σ.toRingHom (conjN E hE x) * D'⁻¹ =
      E * (D' * Mx * D'⁻¹) * E⁻¹ := by
    have hcxm : Matrix.GeneralLinearGroup.map σ.toRingHom (conjN E hE x) =
        Matrix.GeneralLinearGroup.map σ.toRingHom E * Mx *
          (Matrix.GeneralLinearGroup.map σ.toRingHom E)⁻¹ := by
      rw [hcx, Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_mul,
        Matrix.GeneralLinearGroup.map_inv]
    rw [hcxm, hconjE]
    rw [show D' * (E * Mx * E⁻¹) * D'⁻¹ = (D' * E) * Mx * E⁻¹ * D'⁻¹ by group, hD'E]
    rw [show (E * D') * Mx * E⁻¹ * D'⁻¹ = E * D' * Mx * (E⁻¹ * D'⁻¹) by group, hD'Ei]
    group
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hactE x,
    hA (conjN E hE x), hA x]
  set zx : ↥(unitarySU 2 n K d) :=
    ⟨D' * Matrix.GeneralLinearGroup.map σ.toRingHom x * D'⁻¹, hmem x⟩ with hzxdef
  change φ ⟨D' * Matrix.GeneralLinearGroup.map σ.toRingHom (conjN E hE x) * D'⁻¹,
      hmem (conjN E hE x)⟩ = e (φ zx)
  rw [hactE zx]
  congr 1
  apply Subtype.ext
  rw [show ((conjN E hE zx : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = E * zx * E⁻¹ from
    coe_conjN E hE zx, hzxdef]
  simpa [hMxdef] using hkey

end CFSG.StandardType
