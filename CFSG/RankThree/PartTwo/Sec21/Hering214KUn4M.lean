module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KRoot
public import CFSG.RankThree.PartTwo.Sec21.Hering214KEig
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly (IsElemAbelian)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (map_bar_comm)

section UnM

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

abbrev Cid1 (n : ℕ) (K : Type) [Field K] : Matrix (Fin n) (Fin n) K :=
  ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

noncomputable abbrev uB : (Fin n → K) →ₛₗ[h.bar] (Fin n → K) →ₗ[K] K :=
  gramForm h (Cid1 n K)

theorem uB_apply (x y : Fin n → K) : uB h x y = (fun a => h.bar (x a)) ⬝ᵥ y := by
  rw [uB, gramForm_apply, Cid1, Units.val_one, Matrix.one_mulVec]

theorem uB_isSymm : (uB h : (Fin n → K) →ₛₗ[h.bar] (Fin n → K) →ₗ[K] K).IsSymm :=
  gramForm_isSymm h (by
    rw [Cid1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), transpose_one])

noncomputable def uTG {v : Fin n → K} (hv : uB h v v = 0) (c : K) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.toLin.symm (hermTransvectionGL (uB h) hv c)

theorem uTG_mulVec {v : Fin n → K} (hv : uB h v v = 0) (c : K) (x : Fin n → K) :
    ((uTG h hv c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = x + (c * uB h v x) • v := by
  have h1 := Matrix.GeneralLinearGroup.coe_toLin (uTG h hv c)
  have h2 : Matrix.GeneralLinearGroup.toLin (uTG h hv c) = hermTransvectionGL (uB h) hv c :=
    MulEquiv.apply_symm_apply _ _
  rw [← Matrix.mulVecLin_apply, ← h1, h2, coe_hermTransvectionGL, hermTransvection_apply]

theorem gl_ext_mulVec' {g g' : GL (Fin n) K}
    (H : ∀ x, (g : Matrix (Fin n) (Fin n) K) *ᵥ x = (g' : Matrix (Fin n) (Fin n) K) *ᵥ x) :
    g = g' :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, H]))

theorem uTG_add {v : Fin n → K} (hv : uB h v v = 0) (c d : K) :
    uTG h hv c * uTG h hv d = uTG h hv (c + d) := by
  rw [uTG, uTG, uTG, ← map_mul, hermTransvectionGL_mul]

theorem uTG_mem {v : Fin n → K} (hv : uB h v v = 0) {c : K} (hc : c ∈ h.traceZero) :
    uTG h hv c ∈ gramSU h (Cid1 n K) := by
  rw [← toLin_mem_sesqSpecialUnitaryGroup_iff, uTG, MulEquiv.apply_symm_apply]
  exact (hermitian_unitary_transvection h (uB_isSymm h) hv).2.1 c hc

theorem traceZero_of_fixed (c : h.fixedField) : (c : K) ∈ h.traceZero := by
  have hcp : CharP K 2 := h.charP
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace,
    (UnitaryFieldData.mem_fixedField h).mp c.2]
  exact CharTwo.add_self_eq_zero _

noncomputable def uRoot {v : Fin n → K} (hv : uB h v v = 0) (t : h.fixedField) :
    ↥(gramSU h (Cid1 n K)) :=
  ⟨uTG h hv t, uTG_mem h hv (traceZero_of_fixed h t)⟩

theorem uRoot_add {v : Fin n → K} (hv : uB h v v = 0) (s t : h.fixedField) :
    uRoot h hv (s + t) = uRoot h hv s * uRoot h hv t :=
  Subtype.ext (uTG_add h hv s t).symm

theorem uRoot_inj {v : Fin n → K} (hv : uB h v v = 0) (hv0 : v ≠ 0) {s t : h.fixedField}
    (hst : uRoot h hv s = uRoot h hv t) : s = t := by
  have h' : uTG h hv s = uTG h hv t := congrArg Subtype.val hst
  obtain ⟨x, hx⟩ : ∃ x, uB h v x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv0
    have hsep := gramForm_separatingLeft h (G := (Cid1 n K)) (by simp [Cid1])
    exact hsep v hcon
  have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) *ᵥ x) h'
  simp only [uTG_mulVec] at h2
  have h3 : ((s : K) * uB h v x) • v = ((t : K) * uB h v x) • v := add_left_cancel h2
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have h4 := congrFun h3 i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h4 hi
  have h5 : ((s : K) - t) * (uB h v x * v i) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact Subtype.ext (sub_eq_zero.mp h6)
  · exact absurd h6 (mul_ne_zero hx hi)

theorem gl_mulVec_mul' (A B : GL (Fin n) K) (x : Fin n → K) :
    ((A * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
      (A : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ x) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem gl_mulVec_inv_mulVec' (A : GL (Fin n) K) (x : Fin n → K) :
    (A : Matrix (Fin n) (Fin n) K) *ᵥ (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) =
      x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

noncomputable def normFix (l : K) : h.fixedField :=
  ⟨h.norm l, UnitaryFieldData.norm_mem_fixedField h l⟩

theorem uB_isometry_eigen {g : ↥(gramSU h (Cid1 n K))} {v : Fin n → K} {l : K}
    (hl0 : l ≠ 0) (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = l • v)
    (x : Fin n → K) :
    uB h v (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = (h.bar l)⁻¹ * uB h v x := by
  have hiso := (mem_gramSU_iff_isometry.mp g.2).1 v x
  rw [hg, map_smulₛₗ] at hiso
  have hbl : h.bar l ≠ 0 := (map_ne_zero_iff _ h.bar.injective).mpr hl0
  simp only [LinearMap.smul_apply, smul_eq_mul] at hiso
  rw [eq_inv_mul_iff_mul_eq₀ hbl, hiso]

theorem isotropic_of_eigen {g : ↥(gramSU h (Cid1 n K))} {v : Fin n → K}
    {l : K} (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = l • v)
    (hN : h.norm l ≠ 1) : uB h v v = 0 := by
  have hiso := (mem_gramSU_iff_isometry.mp g.2).1 v v
  rw [hg, map_smulₛₗ] at hiso
  simp only [LinearMap.smul_apply, smul_eq_mul, map_smulₛₗ] at hiso
  have h2 : (h.norm l - 1) * uB h v v = 0 := by
    rw [UnitaryFieldData.norm]
    simp only [RingHom.id_apply] at hiso
    linear_combination hiso
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hN
  · exact h3

theorem uRoot_conj {v : Fin n → K} (hv : uB h v v = 0)
    (g : ↥(gramSU h (Cid1 n K))) {l : K} (hl0 : l ≠ 0)
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = l • v) (t : h.fixedField) :
    g * uRoot h hv t * g⁻¹ = uRoot h hv (normFix h l * t) := by
  apply Subtype.ext
  change (g : GL (Fin n) K) * uTG h hv t * (g : GL (Fin n) K)⁻¹ = uTG h hv ((normFix h l * t : _))
  apply gl_ext_mulVec'
  intro x
  rw [gl_mulVec_mul', gl_mulVec_mul', uTG_mulVec, uTG_mulVec]
  set y := (((g : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x with hy
  have hgy : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y = x :=
    gl_mulVec_inv_mulVec' _ x
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hg, ← hgy, uB_isometry_eigen h hl0 hg y]
  have hbl : h.bar l ≠ 0 := (map_ne_zero_iff _ h.bar.injective).mpr hl0
  simp only [normFix, UnitaryFieldData.norm, Subfield.coe_mul, smul_smul]
  congr 2
  field_simp

theorem bar_cube_root {ω l : K} (hω : ω ^ 2 + ω + 1 = 0) (hωb : h.bar ω = ω) (hl3 : l ^ 3 = 1) :
    h.bar l = l := by
  rcases cube_root_cases hω hl3 with e | e | e
  · rw [e, map_one]
  · rw [e, hωb]
  · rw [e, map_pow, hωb]

theorem norm_ne_one_of_cube {ω l : K} (hω : ω ^ 2 + ω + 1 = 0) (hωb : h.bar ω = ω)
    (hl3 : l ^ 3 = 1) (hl1 : l ≠ 1) : h.norm l ≠ 1 := by
  have hb := bar_cube_root h hω hωb hl3
  rw [UnitaryFieldData.norm, hb]
  intro h2
  apply hl1
  calc l = l * (l * l) := by rw [h2, mul_one]
    _ = l ^ 3 := by ring
    _ = 1 := hl3

end UnM

section Un4Four

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem gramSU_mat_pow_three {g : ↥(gramSU h (Cid1 n K))} (hg : g ^ 3 = 1) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 = 1 := by
  have := congrArg
    (fun x : ↥(gramSU h (Cid1 n K)) => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hg
  simpa using this

theorem normFix_pow_three {ω l : K} (hω : ω ^ 2 + ω + 1 = 0) (hωb : h.bar ω = ω)
    (hl3 : l ^ 3 = 1) : normFix h l ^ 3 = 1 := by
  apply Subtype.ext
  have hb := bar_cube_root h hω hωb hl3
  change (h.norm l) ^ 3 = 1
  rw [UnitaryFieldData.norm, hb]
  calc (l * l) ^ 3 = (l ^ 3) ^ 2 := by ring
    _ = 1 := by rw [hl3, one_pow]

theorem normFix_ne_one {ω l : K} (hω : ω ^ 2 + ω + 1 = 0) (hωb : h.bar ω = ω)
    (hl3 : l ^ 3 = 1) (hl1 : l ≠ 1) : normFix h l ≠ 1 := by
  intro hc
  apply norm_ne_one_of_cube h hω hωb hl3 hl1
  exact congrArg Subtype.val hc

theorem un_four_inner {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hωb : h.bar ω = ω)
    {g₁ g₂ : ↥(gramSU h (Cid1 n K))} (h1 : g₁ ^ 3 = 1) (h2 : g₂ ^ 3 = 1)
    (hc : g₁ * g₂ = g₂ * g₁) (h11 : g₁ ≠ 1) :
    ∃ W : Subgroup ↥(gramSU h (Cid1 n K)), IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      (∀ w ∈ W, g₁ * w * g₁⁻¹ ∈ W) ∧ (∀ w ∈ W, g₂ * w * g₂⁻¹ ∈ W) ∧
      ∃ w ∈ W, g₁ * w * g₁⁻¹ ≠ w := by
  haveI : CharP K 2 := h.charP
  have hMN : ((g₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := congrArg
      (fun x : ↥(gramSU h (Cid1 n K)) => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hc
    simpa using this
  have hM1 : ((g₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ 1 :=
    fun e => h11 (Subtype.ext (Units.ext e))
  obtain ⟨v, l, m, hv0, hMv, hNv, hl3, hm3, hl1⟩ := exists_joint_eigenvector hω hω1
    (gramSU_mat_pow_three h h1) (gramSU_mat_pow_three h h2) hMN hM1
  have hv : uB h v v = 0 := isotropic_of_eigen h hMv (norm_ne_one_of_cube h hω hωb hl3 hl1)
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl3
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm3
  let ω' : h.fixedField := ⟨ω, (UnitaryFieldData.mem_fixedField h).mpr hωb⟩
  have hω' : ω' ^ 2 + ω' + 1 = 0 := Subtype.ext (by simpa [ω'] using hω)
  have hω'1 : ω' ≠ 1 := fun e => hω1 (by simpa [ω'] using congrArg Subtype.val e)
  have hmul := uRoot_add h hv
  have hinj : ∀ s t, uRoot h hv s = uRoot h hv t → s = t := fun s t e => uRoot_inj h hv hv0 e
  refine ⟨rootFourOf (uRoot h hv) ω', (rootFourOf_spec hmul hinj hω' hω'1).1,
    (rootFourOf_spec hmul hinj hω' hω'1).2,
    rootFourOf_normalized hmul hω' (normFix_pow_three h hω hωb hl3)
      (uRoot_conj h hv g₁ hl0 hMv),
    rootFourOf_normalized hmul hω' (normFix_pow_three h hω hωb hm3)
      (uRoot_conj h hv g₂ hm0 hNv),
    uRoot h hv 1, mem_rootFourOf_one ω',
    rootFourOf_moved hinj (normFix_ne_one h hω hωb hl3 hl1) (uRoot_conj h hv g₁ hl0 hMv)⟩

theorem uTG_map_fixed {v : Fin n → K} (hv : uB h v v = 0) (σ : K ≃+* K)
    (hσv : ∀ i, σ (v i) = v i) {c : K} (hσc : σ c = c) :
    ((uTG h hv c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ =
      ((uTG h hv c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ : ∃ x : Fin n → K, y = fun i => σ (x i) :=
    ⟨fun i => σ.symm (y i), by funext i; simp⟩
  have hB : σ (uB h v x) = uB h v (fun i => σ (x i)) := by
    simp only [uB_apply, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_bar_comm h σ, hσv]
  have h1 : ∀ i, σ ((((uTG h hv c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) i) =
      ((((uTG h hv c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ) *ᵥ
        (fun i => σ (x i))) i := fun i => RingHom.map_mulVec σ.toRingHom _ x i
  simp only [Matrix.toLin'_apply]
  funext i
  rw [← h1 i, uTG_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hσc, hB, hσv]
  rw [uTG_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem un_four_fixed {σ : K ≃+* K} {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (hωb : h.bar ω = ω) (hσω : σ ω = ω) {g : ↥(gramSU h (Cid1 n K))} (h3 : g ^ 3 = 1)
    (hg1 : g ≠ 1)
    (hfix : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ W : Subgroup ↥(gramSU h (Cid1 n K)), IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      (∀ w ∈ W, ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ =
        ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧
      (∀ w ∈ W, g * w * g⁻¹ ∈ W) ∧ ∃ w ∈ W, g * w * g⁻¹ ≠ w := by
  haveI : CharP K 2 := h.charP
  have hM := gramSU_mat_pow_three h h3
  have hM1 : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠ 1 :=
    fun e => hg1 (Subtype.ext (Units.ext e))
  obtain ⟨v, l, m, hv0, hvσ, hMv, -, hl3, -, hl1⟩ := exists_joint_eigenvector_fixed hω hω1 hσω hM
    hM rfl hM1 hfix hfix
  have hv : uB h v v = 0 := isotropic_of_eigen h hMv (norm_ne_one_of_cube h hω hωb hl3 hl1)
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl3
  let ω' : h.fixedField := ⟨ω, (UnitaryFieldData.mem_fixedField h).mpr hωb⟩
  have hω' : ω' ^ 2 + ω' + 1 = 0 := Subtype.ext (by simpa [ω'] using hω)
  have hω'1 : ω' ≠ 1 := fun e => hω1 (by simpa [ω'] using congrArg Subtype.val e)
  have hmul := uRoot_add h hv
  have hinj : ∀ s t, uRoot h hv s = uRoot h hv t → s = t := fun s t e => uRoot_inj h hv hv0 e
  have hfixroot : ∀ t : h.fixedField, σ (t : K) = t →
      Matrix.GeneralLinearGroup.map (σ : K →+* K) ((uRoot h hv t : GL (Fin n) K)) =
        (uRoot h hv t : GL (Fin n) K) := by
    intro t ht
    apply Units.ext
    exact uTG_map_fixed h hv σ hvσ ht
  refine ⟨rootFourOf (uRoot h hv) ω', (rootFourOf_spec hmul hinj hω' hω'1).1,
    (rootFourOf_spec hmul hinj hω' hω'1).2, ?_,
    rootFourOf_normalized hmul hω' (normFix_pow_three h hω hωb hl3)
      (uRoot_conj h hv g hl0 hMv),
    uRoot h hv 1, mem_rootFourOf_one ω',
    rootFourOf_moved hinj (normFix_ne_one h hω hωb hl3 hl1) (uRoot_conj h hv g hl0 hMv)⟩
  let Fix : Subgroup ↥(gramSU h (Cid1 n K)) :=
    MonoidHom.eqLocus
      ((Matrix.GeneralLinearGroup.map (σ : K →+* K)).comp (gramSU h (Cid1 n K)).subtype)
      (gramSU h (Cid1 n K)).subtype
  have hW : rootFourOf (uRoot h hv) ω' ≤ Fix := by
    rw [rootFourOf, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hfixroot 1 (map_one σ)
    · exact hfixroot ω' hσω
  intro w hw
  exact congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) (hW hw)

end Un4Four

end CFSG.RankThree.PartTwo.Sec21.Hering214
