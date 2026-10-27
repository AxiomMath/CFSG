module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableDefs
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.OrthRot

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.ClassicalEven.OrthRot
open scoped Matrix

private theorem s15k_tsl_single_eq_of_ne {n : ℕ} {i i' : Fin n} (h : i' ≠ i) :
    (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) i' = 0 :=
  Pi.single_eq_of_ne h 1

section SLVectorRank

variable {n : ℕ}

private noncomputable def s15k_tsl_c1 (m : Fin n → ZMod 2) (j a b : Fin n) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj a : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) +
    (LinearMap.proj b : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) +
    (m a + m b) • (LinearMap.proj j : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)

private noncomputable def s15k_tsl_c2 (m : Fin n → ZMod 2) (j a : Fin n) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj a : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) +
    m a • (LinearMap.proj j : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)

private noncomputable def s15k_tsl_rot (m : Fin n → ZMod 2) (j a b : Fin n) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearMap.id + (s15k_tsl_c1 m j a b).smulRight (Pi.single a 1) +
    (s15k_tsl_c2 m j a).smulRight (Pi.single b 1)

private theorem s15k_tsl_rot_apply (m : Fin n → ZMod 2) (j a b : Fin n)
    (v : Fin n → ZMod 2) :
    s15k_tsl_rot m j a b v =
      v + s15k_tsl_c1 m j a b v • Pi.single a 1 +
        s15k_tsl_c2 m j a v • Pi.single b 1 := rfl

private theorem s15k_tsl_c1_apply (m : Fin n → ZMod 2) (j a b : Fin n)
    (v : Fin n → ZMod 2) :
    s15k_tsl_c1 m j a b v = v a + v b + (m a + m b) * v j := by
  simp [s15k_tsl_c1, smul_eq_mul]

private theorem s15k_tsl_c2_apply (m : Fin n → ZMod 2) (j a : Fin n)
    (v : Fin n → ZMod 2) :
    s15k_tsl_c2 m j a v = v a + m a * v j := by
  simp [s15k_tsl_c2, smul_eq_mul]

private theorem s15k_tsl_rot_apply_a {m : Fin n → ZMod 2} {j a b : Fin n} (hab : a ≠ b)
    (v : Fin n → ZMod 2) :
    s15k_tsl_rot m j a b v a = v a + s15k_tsl_c1 m j a b v := by
  rw [s15k_tsl_rot_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
    s15k_tsl_single_eq_of_ne hab, mul_zero, mul_one, add_zero]

private theorem s15k_tsl_rot_apply_b {m : Fin n → ZMod 2} {j a b : Fin n} (hab : a ≠ b)
    (v : Fin n → ZMod 2) :
    s15k_tsl_rot m j a b v b = v b + s15k_tsl_c2 m j a v := by
  rw [s15k_tsl_rot_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
    s15k_tsl_single_eq_of_ne hab.symm, mul_zero, mul_one, add_zero]

private theorem s15k_tsl_rot_apply_of_ne {m : Fin n → ZMod 2} {j a b : Fin n} {i : Fin n}
    (hia : i ≠ a) (hib : i ≠ b) (v : Fin n → ZMod 2) :
    s15k_tsl_rot m j a b v i = v i := by
  rw [s15k_tsl_rot_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, s15k_tsl_single_eq_of_ne hia,
    s15k_tsl_single_eq_of_ne hib, mul_zero, add_zero]

private theorem s15k_tsl_c1_rot {m : Fin n → ZMod 2} {j a b : Fin n}
    (hja : j ≠ a) (hjb : j ≠ b) (hab : a ≠ b) (v : Fin n → ZMod 2) :
    s15k_tsl_c1 m j a b (s15k_tsl_rot m j a b v) = s15k_tsl_c2 m j a v := by
  rw [s15k_tsl_c1_apply, s15k_tsl_rot_apply_a hab, s15k_tsl_rot_apply_b hab,
    s15k_tsl_rot_apply_of_ne hja hjb, s15k_tsl_c1_apply, s15k_tsl_c2_apply]
  generalize v a = x
  generalize v b = y
  generalize v j = z
  generalize m a = p
  generalize m b = q
  decide +revert

private theorem s15k_tsl_c2_rot {m : Fin n → ZMod 2} {j a b : Fin n}
    (hja : j ≠ a) (hjb : j ≠ b) (hab : a ≠ b) (v : Fin n → ZMod 2) :
    s15k_tsl_c2 m j a (s15k_tsl_rot m j a b v) =
      s15k_tsl_c1 m j a b v + s15k_tsl_c2 m j a v := by
  rw [s15k_tsl_c2_apply, s15k_tsl_rot_apply_a hab, s15k_tsl_rot_apply_of_ne hja hjb,
    s15k_tsl_c1_apply, s15k_tsl_c2_apply]
  generalize v a = x
  generalize v b = y
  generalize v j = z
  generalize m a = p
  generalize m b = q
  decide +revert

private theorem s15k_tsl_rot_comp_three {m : Fin n → ZMod 2} {j a b : Fin n}
    (hja : j ≠ a) (hjb : j ≠ b) (hab : a ≠ b) :
    (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
        (s15k_tsl_rot m j a b)) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [s15k_tsl_rot_apply]
  rw [s15k_tsl_c1_rot hja hjb hab (s15k_tsl_rot m j a b v)]
  rw [s15k_tsl_c2_rot hja hjb hab (s15k_tsl_rot m j a b v)]
  rw [s15k_tsl_rot_apply]
  simp only [s15k_tsl_c1_rot hja hjb hab v, s15k_tsl_c2_rot hja hjb hab v]
  rw [s15k_tsl_rot_apply]
  simp only [s15k_tsl_c1_apply, s15k_tsl_c2_apply]
  funext i
  by_cases hia : i = a
  · rw [hia]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      s15k_tsl_single_eq_of_ne hab, mul_zero, mul_one, add_zero]
    generalize v a = x
    generalize v b = y
    generalize v j = z
    generalize m a = p
    generalize m b = q
    decide +revert
  · by_cases hib : i = b
    · rw [hib]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
        s15k_tsl_single_eq_of_ne hab.symm, mul_zero, mul_one, add_zero]
      generalize v a = x
      generalize v b = y
      generalize v j = z
      generalize m a = p
      generalize m b = q
      decide +revert
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        s15k_tsl_single_eq_of_ne hia, s15k_tsl_single_eq_of_ne hib, mul_zero,
        add_zero, CharTwo.add_self_eq_zero]

private theorem s15k_tsl_rot_single_a {m : Fin n → ZMod 2} {j a b : Fin n}
    (hja : j ≠ a) (hjb : j ≠ b) (hab : a ≠ b) :
    s15k_tsl_rot m j a b (Pi.single a 1) = Pi.single b 1 := by
  rw [s15k_tsl_rot_apply, s15k_tsl_c1_apply, s15k_tsl_c2_apply]
  have hc1 : (Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) a +
      (Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) b +
      (m a + m b) * (Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) j = 1 := by
    rw [Pi.single_eq_same, s15k_tsl_single_eq_of_ne hab.symm,
      s15k_tsl_single_eq_of_ne hja]
    ring
  have hc2 : (Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) a +
      m a * (Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) j = 1 := by
    rw [Pi.single_eq_same, s15k_tsl_single_eq_of_ne hja]
    ring
  rw [hc1, hc2, one_smul, one_smul]
  have hself : (Pi.single a (1 : ZMod 2) + Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) = 0 := by
    funext t
    exact CharTwo.add_self_eq_zero ((Pi.single a (1 : ZMod 2) : Fin n → ZMod 2) t)
  rw [hself, zero_add]

private theorem s15k_tsl_rot_fix_single {m : Fin n → ZMod 2} {j a b i : Fin n}
    (hia : i ≠ a) (hib : i ≠ b) (hij : i ≠ j) :
    s15k_tsl_rot m j a b (Pi.single i 1) = Pi.single i 1 := by
  rw [s15k_tsl_rot_apply]
  have hc1 : s15k_tsl_c1 m j a b (Pi.single i 1) = 0 := by
    rw [s15k_tsl_c1_apply, s15k_tsl_single_eq_of_ne (Ne.symm hia),
      s15k_tsl_single_eq_of_ne (Ne.symm hib),
      s15k_tsl_single_eq_of_ne (Ne.symm hij)]
    ring
  have hc2 : s15k_tsl_c2 m j a (Pi.single i 1) = 0 := by
    rw [s15k_tsl_c2_apply, s15k_tsl_single_eq_of_ne (Ne.symm hia),
      s15k_tsl_single_eq_of_ne (Ne.symm hij)]
    ring
  simp only [hc1, hc2, zero_smul, add_zero]

private theorem s15k_tsl_c1_self {m : Fin n → ZMod 2} {j a b : Fin n}
    (hmj : m j = 1 ∨ m = 0) : s15k_tsl_c1 m j a b m = 0 := by
  rcases hmj with hmj | hm
  · rw [s15k_tsl_c1_apply, hmj, mul_one]
    generalize m a = x
    generalize m b = y
    decide +revert
  · simp [hm, s15k_tsl_c1]

private theorem s15k_tsl_c2_self {m : Fin n → ZMod 2} {j a : Fin n}
    (hmj : m j = 1 ∨ m = 0) : s15k_tsl_c2 m j a m = 0 := by
  rcases hmj with hmj | hm
  · rw [s15k_tsl_c2_apply, hmj, mul_one]
    generalize m a = x
    decide +revert
  · simp [hm, s15k_tsl_c2]

private theorem s15k_tsl_rot_fix_m {m : Fin n → ZMod 2} {j a b : Fin n}
    (hmj : m j = 1 ∨ m = 0) : s15k_tsl_rot m j a b m = m := by
  rw [s15k_tsl_rot_apply]
  simp only [s15k_tsl_c1_self hmj, s15k_tsl_c2_self hmj, zero_smul, add_zero]

private noncomputable def s15k_tsl_rotEquiv {m : Fin n → ZMod 2} {j a b : Fin n}
    (h : (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
        (s15k_tsl_rot m j a b)) = LinearMap.id) :
    (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun := s15k_tsl_rot m j a b
  invFun := (s15k_tsl_rot m j a b).comp (s15k_tsl_rot m j a b)
  left_inv v := by
    have hv := congrArg (fun L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) => L v) h
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hv
  right_inv v := by
    have hv := congrArg (fun L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) => L v) h
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using hv
  map_add' := (s15k_tsl_rot m j a b).map_add
  map_smul' := (s15k_tsl_rot m j a b).map_smul

private noncomputable def s15k_tsl_rotGL {m : Fin n → ZMod 2} {j a b : Fin n}
    (h : (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
        (s15k_tsl_rot m j a b)) = LinearMap.id) :
    Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
  let L := s15k_tsl_rotEquiv h
  ⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp, L.comp_symm, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, L.symm_comp, LinearMap.toMatrix'_id]⟩

private theorem s15k_tsl_rotGL_mulVec {m : Fin n → ZMod 2} {j a b : Fin n}
    (h : (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
        (s15k_tsl_rot m j a b)) = LinearMap.id) (v : Fin n → ZMod 2) :
    (s15k_tsl_rotGL h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = s15k_tsl_rot m j a b v := by
  change LinearMap.toMatrix' (s15k_tsl_rot m j a b) *ᵥ v = s15k_tsl_rot m j a b v
  exact LinearMap.toMatrix'_mulVec _ v

private theorem s15k_tsl_rotGL_pow_three {m : Fin n → ZMod 2} {j a b : Fin n}
    (h : (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
        (s15k_tsl_rot m j a b)) = LinearMap.id) :
    s15k_tsl_rotGL h ^ 3 = 1 := by
  apply gl_ext
  intro v
  rw [pow_three, mul_mulVec, mul_mulVec, Units.val_one, Matrix.one_mulVec]
  simp only [s15k_tsl_rotGL_mulVec]
  exact congrArg (fun L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) => L v) h

private theorem s15k_tsl_rotGL_mem {m : Fin n → ZMod 2} {j a b : Fin n}
    (h : (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
        (s15k_tsl_rot m j a b)) = LinearMap.id) (hmj : m j = 1 ∨ m = 0) :
    s15k_tsl_rotGL h ∈ s15kVecStab m := by
  change (s15k_tsl_rotGL h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ m = m
  rw [s15k_tsl_rotGL_mulVec, s15k_tsl_rot_fix_m hmj]

private theorem s15k_tsl_rotGL_ne_one {m : Fin n → ZMod 2} {j a b : Fin n}
    (hja : j ≠ a) (hjb : j ≠ b) (hab : a ≠ b)
    (h : (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
        (s15k_tsl_rot m j a b)) = LinearMap.id) :
    s15k_tsl_rotGL h ≠ 1 := by
  intro heq
  have h1 : (s15k_tsl_rotGL h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a 1 =
      Pi.single b 1 := by
    rw [s15k_tsl_rotGL_mulVec, s15k_tsl_rot_single_a hja hjb hab]
  rw [heq, Units.val_one, Matrix.one_mulVec] at h1
  have h2 := congrFun h1 a
  rw [Pi.single_eq_same, s15k_tsl_single_eq_of_ne hab] at h2
  exact one_ne_zero h2

private theorem s15k_tsl_c1_fixrot {m : Fin n → ZMod 2} {j a b a' b' : Fin n}
    (haa' : a ≠ a') (hab' : a ≠ b') (hba' : b ≠ a') (hbb' : b ≠ b')
    (hja' : j ≠ a') (hjb' : j ≠ b') (v : Fin n → ZMod 2) :
    s15k_tsl_c1 m j a b (s15k_tsl_rot m j a' b' v) = s15k_tsl_c1 m j a b v := by
  rw [s15k_tsl_c1_apply, s15k_tsl_rot_apply_of_ne haa' hab',
    s15k_tsl_rot_apply_of_ne hba' hbb', s15k_tsl_rot_apply_of_ne hja' hjb', s15k_tsl_c1_apply]

private theorem s15k_tsl_c2_fixrot {m : Fin n → ZMod 2} {j a a' b' : Fin n}
    (haa' : a ≠ a') (hab' : a ≠ b') (hja' : j ≠ a') (hjb' : j ≠ b')
    (v : Fin n → ZMod 2) :
    s15k_tsl_c2 m j a (s15k_tsl_rot m j a' b' v) = s15k_tsl_c2 m j a v := by
  rw [s15k_tsl_c2_apply, s15k_tsl_rot_apply_of_ne haa' hab',
    s15k_tsl_rot_apply_of_ne hja' hjb', s15k_tsl_c2_apply]

private theorem s15k_tsl_rot_comm {m : Fin n → ZMod 2} {j a b a' b' : Fin n}
    (hab : a ≠ b) (ha'b' : a' ≠ b')
    (haa' : a ≠ a') (hab' : a ≠ b') (hba' : b ≠ a') (hbb' : b ≠ b')
    (hja' : j ≠ a') (hjb' : j ≠ b')
    (ha'a : a' ≠ a) (ha'b : a' ≠ b) (hb'a : b' ≠ a) (hb'b : b' ≠ b)
    (hja : j ≠ a) (hjb : j ≠ b) (v : Fin n → ZMod 2) :
    s15k_tsl_rot m j a b (s15k_tsl_rot m j a' b' v) =
      s15k_tsl_rot m j a' b' (s15k_tsl_rot m j a b v) := by
  rw [s15k_tsl_rot_apply]
  rw [s15k_tsl_c1_fixrot haa' hab' hba' hbb' hja' hjb' v,
    s15k_tsl_c2_fixrot haa' hab' hja' hjb' v]
  rw [s15k_tsl_rot_apply]
  rw [s15k_tsl_rot_apply]
  rw [s15k_tsl_c1_fixrot ha'a ha'b hb'a hb'b hja hjb v,
    s15k_tsl_c2_fixrot ha'a ha'b hja hjb v]
  rw [s15k_tsl_rot_apply]
  abel

private theorem s15k_tsl_rotGL_commute {m : Fin n → ZMod 2} {j a b a' b' : Fin n}
    (hab : a ≠ b) (ha'b' : a' ≠ b')
    (haa' : a ≠ a') (hab' : a ≠ b') (hba' : b ≠ a') (hbb' : b ≠ b')
    (hja' : j ≠ a') (hjb' : j ≠ b')
    (ha'a : a' ≠ a) (ha'b : a' ≠ b) (hb'a : b' ≠ a) (hb'b : b' ≠ b)
    (hja : j ≠ a) (hjb : j ≠ b)
    (h : (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
        (s15k_tsl_rot m j a b)) = LinearMap.id)
    (h' : (s15k_tsl_rot m j a' b').comp ((s15k_tsl_rot m j a' b').comp
        (s15k_tsl_rot m j a' b')) = LinearMap.id) :
    Commute (s15k_tsl_rotGL h) (s15k_tsl_rotGL h') :=
  gl_ext fun v => by
    simp only [mul_mulVec, s15k_tsl_rotGL_mulVec]
    exact s15k_tsl_rot_comm hab ha'b' haa' hab' hba' hbb' hja' hjb' ha'a ha'b hb'a hb'b hja hjb v

private theorem s15k_tsl_rotGL_pow_ne {m : Fin n → ZMod 2} {j a b a' b' : Fin n}
    (ha'a : a' ≠ a) (ha'b : a' ≠ b) (ha'j : a' ≠ j)
    (hja' : j ≠ a') (hjb' : j ≠ b') (ha'b' : a' ≠ b')
    (h : (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
        (s15k_tsl_rot m j a b)) = LinearMap.id)
    (h' : (s15k_tsl_rot m j a' b').comp ((s15k_tsl_rot m j a' b').comp
        (s15k_tsl_rot m j a' b')) = LinearMap.id) (k : ℕ) :
    s15k_tsl_rotGL h ^ k ≠ s15k_tsl_rotGL h' := by
  intro heq
  have hfix : (s15k_tsl_rotGL h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a' 1 =
      Pi.single a' 1 := by
    rw [s15k_tsl_rotGL_mulVec, s15k_tsl_rot_fix_single ha'a ha'b ha'j]
  have h1 : ((s15k_tsl_rotGL h ^ k : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a' 1 = Pi.single a' 1 :=
    pow_mulVec_of_fix hfix k
  have h2 : (s15k_tsl_rotGL h' : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single a' 1 =
      Pi.single b' 1 := by
    rw [s15k_tsl_rotGL_mulVec, s15k_tsl_rot_single_a hja' hjb' ha'b']
  rw [heq, h2] at h1
  have h3 := congrFun h1 a'
  rw [Pi.single_eq_same, s15k_tsl_single_eq_of_ne ha'b'] at h3
  exact one_ne_zero h3.symm

end SLVectorRank

private theorem s15k_tsl_fin_ne {n a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    (⟨a, ha⟩ : Fin n) ≠ ⟨b, hb⟩ :=
  fun h => hab (congrArg Fin.val h)

theorem s15k_table_sl_rank {n : ℕ} (hn : 3 ≤ n) (m : Fin n → ZMod 2) :
    1 ≤ pRank 3 (s15kVecStab m) ∧ (5 ≤ n → 2 ≤ pRank 3 (s15kVecStab m)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hn' : 2 ≤ n' := by omega
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hex : ∃ j : Fin (n' + 1), m j = 1 ∨ m = 0 := by
    by_cases hm : m = 0
    · exact ⟨⟨0, by omega⟩, Or.inr hm⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
      exact ⟨i, Or.inl (h01 _ hi)⟩
  obtain ⟨j, hj⟩ := hex
  let a : Fin (n' + 1) := j.succAbove ⟨0, by omega⟩
  let b : Fin (n' + 1) := j.succAbove ⟨1, by omega⟩
  have hja : j ≠ a := (Fin.succAbove_ne j ⟨0, by omega⟩).symm
  have hjb : j ≠ b := (Fin.succAbove_ne j ⟨1, by omega⟩).symm
  have hab : a ≠ b := fun h =>
    s15k_tsl_fin_ne (by omega) (by omega) (by omega) (Fin.succAbove_right_injective h)
  have hcomp : (s15k_tsl_rot m j a b).comp ((s15k_tsl_rot m j a b).comp
      (s15k_tsl_rot m j a b)) = LinearMap.id := s15k_tsl_rot_comp_three hja hjb hab
  let x : Matrix.GeneralLinearGroup (Fin (n' + 1)) (ZMod 2) := s15k_tsl_rotGL hcomp
  have hxH : x ∈ s15kVecStab m := s15k_tsl_rotGL_mem hcomp hj
  have hx3 : x ^ 3 = 1 := s15k_tsl_rotGL_pow_three hcomp
  have hx1 : x ≠ 1 := s15k_tsl_rotGL_ne_one hja hjb hab hcomp
  refine ⟨s15k_table_one_le_pRank hxH hx3 hx1, ?_⟩
  intro h5
  have hn'4 : 4 ≤ n' := by omega
  let a' : Fin (n' + 1) := j.succAbove ⟨2, by omega⟩
  let b' : Fin (n' + 1) := j.succAbove ⟨3, by omega⟩
  have hja' : j ≠ a' := (Fin.succAbove_ne j ⟨2, by omega⟩).symm
  have hjb' : j ≠ b' := (Fin.succAbove_ne j ⟨3, by omega⟩).symm
  have ha'b' : a' ≠ b' := fun h =>
    s15k_tsl_fin_ne (by omega) (by omega) (by omega) (Fin.succAbove_right_injective h)
  have hcomp' : (s15k_tsl_rot m j a' b').comp ((s15k_tsl_rot m j a' b').comp
      (s15k_tsl_rot m j a' b')) = LinearMap.id := s15k_tsl_rot_comp_three hja' hjb' ha'b'
  let y : Matrix.GeneralLinearGroup (Fin (n' + 1)) (ZMod 2) := s15k_tsl_rotGL hcomp'
  have hyH : y ∈ s15kVecStab m := s15k_tsl_rotGL_mem hcomp' hj
  have hy3 : y ^ 3 = 1 := s15k_tsl_rotGL_pow_three hcomp'
  have haa' : a ≠ a' := fun h =>
    s15k_tsl_fin_ne (by omega) (by omega) (by omega) (Fin.succAbove_right_injective h)
  have hab' : a ≠ b' := fun h =>
    s15k_tsl_fin_ne (by omega) (by omega) (by omega) (Fin.succAbove_right_injective h)
  have hba' : b ≠ a' := fun h =>
    s15k_tsl_fin_ne (by omega) (by omega) (by omega) (Fin.succAbove_right_injective h)
  have hbb' : b ≠ b' := fun h =>
    s15k_tsl_fin_ne (by omega) (by omega) (by omega) (Fin.succAbove_right_injective h)
  have ha'a : a' ≠ a := haa'.symm
  have ha'b : a' ≠ b := hba'.symm
  have hb'a : b' ≠ a := hab'.symm
  have hb'b : b' ≠ b := hbb'.symm
  have hcomm : Commute x y :=
    s15k_tsl_rotGL_commute hab ha'b' haa' hab' hba' hbb' hja' hjb' ha'a ha'b hb'a hb'b hja hjb
      hcomp hcomp'
  have hne : ∀ k : ℕ, x ^ k ≠ y := fun k =>
    s15k_tsl_rotGL_pow_ne ha'a ha'b hja'.symm hja' hjb' ha'b' hcomp hcomp' k
  exact s15k_table_two_le_pRank hxH hyH hx3 hy3 hcomm hx1 hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
