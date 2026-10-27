module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic
public import CFSG.LieType.Steinberg.Minuscule.RankOne

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

@[expose] def V0 (K : Type) [Field K] : Submodule K (V K) := Finsupp.supported K K (idx0 : Set (Fin e7Data.d))

theorem mem_V0 {K : Type} [Field K] {v : V K} : v ∈ V0 K ↔ ∀ b, b ∉ idx0 → v b = 0 := by
  unfold V0
  rw [Finsupp.mem_supported']
  simp

variable {K : Type} [Field K]

@[expose] def jFun (m : Matrix (Fin 2) (Fin 2) K) (v : Fin e7Data.d → K) (b : Fin e7Data.d) : K :=
  if pr b theta = 0 then v b
  else if pr b theta = -1 then m 0 0 * v b + m 0 1 * v (shift theta b)
  else m 1 0 * v (shift (-theta) b) + m 1 1 * v b

@[expose] def jOp (m : Matrix (Fin 2) (Fin 2) K) : V K →ₗ[K] V K where
  toFun v := Finsupp.equivFunOnFinite.symm (jFun m ⇑v)
  map_add' v w := by
    ext b
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_add, Pi.add_apply, jFun]
    split_ifs <;> ring
  map_smul' c v := by
    ext b
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, jFun]
    split_ifs <;> ring

theorem jOp_apply (m : Matrix (Fin 2) (Fin 2) K) (v : V K) (b : Fin e7Data.d) :
    jOp m v b = jFun m ⇑v b := by
  simp [jOp]

theorem jFun_of_zero {m : Matrix (Fin 2) (Fin 2) K} {v : Fin e7Data.d → K} {b : Fin e7Data.d}
    (h : pr b theta = 0) : jFun m v b = v b := by
  unfold jFun
  rw [if_pos h]

theorem jFun_of_neg {m : Matrix (Fin 2) (Fin 2) K} {v : Fin e7Data.d → K} {b : Fin e7Data.d}
    (h : pr b theta = -1) :
    jFun m v b = m 0 0 * v b + m 0 1 * v (shift theta b) := by
  unfold jFun
  rw [if_neg (show ¬ (pr b theta = 0) by omega), if_pos h]

theorem jFun_of_pos {m : Matrix (Fin 2) (Fin 2) K} {v : Fin e7Data.d → K} {b : Fin e7Data.d}
    (h : pr b theta = 1) :
    jFun m v b = m 1 0 * v (shift (-theta) b) + m 1 1 * v b := by
  unfold jFun
  rw [if_neg (show ¬ (pr b theta = 0) by omega), if_neg (show ¬ (pr b theta = -1) by omega)]

theorem jOp_one : jOp (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro b
  rw [jOp_apply, Module.End.one_apply]
  rcases pr_mem isRoot_theta b with h | h | h
  · rw [jFun_of_neg h]
    simp [Matrix.one_apply]
  · rw [jFun_of_zero h]
  · rw [jFun_of_pos h]
    simp [Matrix.one_apply]

theorem jOp_mul (m m' : Matrix (Fin 2) (Fin 2) K) : jOp (m * m') = jOp m * jOp m' := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro b
  have hw : ⇑(jOp m' v) = jFun m' ⇑v := funext fun c => jOp_apply m' v c
  rw [Module.End.mul_apply, jOp_apply, jOp_apply, hw]
  rcases pr_mem isRoot_theta b with h | h | h
  · simp only [jFun_of_neg h, jFun_of_pos (pr_shift_self isRoot_theta h),
      shift_neg_shift isRoot_theta h, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp only [jFun_of_zero h]
  · simp only [jFun_of_pos h, jFun_of_neg (pr_shift_neg isRoot_theta h),
      shift_shift_neg isRoot_theta h, Matrix.mul_apply, Fin.sum_univ_two]
    ring

@[expose] def jHom : Matrix.SpecialLinearGroup (Fin 2) K →* (Module.End K (V K))ˣ where
  toFun m := ⟨jOp (m : Matrix (Fin 2) (Fin 2) K), jOp ((m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K), by rw [← jOp_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, jOp_one], by
      rw [← jOp_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, jOp_one]⟩
  map_one' := by
    ext1
    simp [jOp_one]
  map_mul' m m' := by
    ext1
    simp [jOp_mul]

theorem jHom_val (m : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((jHom m : (Module.End K (V K))ˣ) : Module.End K (V K)) = jOp (m : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem xu_theta [CharP K 2] (c : K) : e7Data_valid.xu K theta c = jHom (MinData.Valid.slLower K c) := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro b
  rw [xu_apply_coord isRoot_theta, jHom_val, jOp_apply, MinData.Valid.slLower_val]
  unfold jFun
  rcases pr_mem isRoot_theta b with h | h | h <;> simp [h] <;> ring

theorem xu_neg_theta [CharP K 2] (c : K) : e7Data_valid.xu K (-theta) c = jHom (MinData.Valid.slUpper K c) := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro b
  rw [xu_apply_coord (isRoot_neg isRoot_theta), jHom_val, jOp_apply, MinData.Valid.slUpper_val,
    neg_neg, pr_neg]
  unfold jFun
  rcases pr_mem isRoot_theta b with h | h | h <;> simp [h] <;> ring

@[expose] def Jgrp (K : Type) [Field K] : Subgroup (Module.End K (V K))ˣ :=
  Subgroup.closure {g | ∃ c : K, g = e7Data_valid.xu K theta c ∨ g = e7Data_valid.xu K (-theta) c}

private theorem sl2_eq_upper_lower_upper (s : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : (s : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    s = MinData.Valid.slUpper K (((s : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) /
        (s : Matrix (Fin 2) (Fin 2) K) 1 0) *
      MinData.Valid.slLower K ((s : Matrix (Fin 2) (Fin 2) K) 1 0) *
      MinData.Valid.slUpper K (((s : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) /
        (s : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  have hdet := s.2
  rw [Matrix.det_fin_two] at hdet
  ext x y
  simp only [Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slUpper_val,
    MinData.Valid.slLower_val]
  fin_cases x <;> fin_cases y
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    linear_combination (-1 : K) * hdet
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring

theorem sl2_eq_prod (m : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ e a b c : K, m = MinData.Valid.slLower K e * MinData.Valid.slUpper K a * MinData.Valid.slLower K b * MinData.Valid.slUpper K c := by
  have hlow0 : MinData.Valid.slLower K (0 : K) = 1 := by
    ext x y
    fin_cases x <;> fin_cases y <;> rfl
  by_cases h : (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · set s' := MinData.Valid.slLower K (1 : K) * m with hs'_def
    have hdet := m.2
    rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
    have h' : (s' : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      simp only [s', Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slLower_val, Matrix.mul_apply,
        Fin.sum_univ_two]
      simp [h]
      exact left_ne_zero_of_mul_eq_one hdet
    have hs' := sl2_eq_upper_lower_upper s' h'
    refine ⟨-1, ((s' : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (s' : Matrix (Fin 2) (Fin 2) K) 1 0,
      (s' : Matrix (Fin 2) (Fin 2) K) 1 0,
      ((s' : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (s' : Matrix (Fin 2) (Fin 2) K) 1 0, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_assoc (MinData.Valid.slUpper K _), ← hs', hs'_def, ← mul_assoc,
      show MinData.Valid.slLower K (-1 : K) * MinData.Valid.slLower K 1 = 1 by
        ext x y
        fin_cases x <;> fin_cases y <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, MinData.Valid.slLower_val],
      one_mul]
  · refine ⟨0, ((m : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) / (m : Matrix (Fin 2) (Fin 2) K) 1 0,
      (m : Matrix (Fin 2) (Fin 2) K) 1 0,
      ((m : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) / (m : Matrix (Fin 2) (Fin 2) K) 1 0, ?_⟩
    rw [hlow0, one_mul]
    exact sl2_eq_upper_lower_upper m h

theorem Jgrp_eq_range [CharP K 2] : Jgrp K = (jHom (K := K)).range := by
  apply le_antisymm
  · rw [Jgrp, Subgroup.closure_le]
    rintro g ⟨c, rfl | rfl⟩
    · exact MonoidHom.mem_range.2 ⟨MinData.Valid.slLower K c, (xu_theta c).symm⟩
    · exact MonoidHom.mem_range.2 ⟨MinData.Valid.slUpper K c, (xu_neg_theta c).symm⟩
  · rintro g ⟨m, rfl⟩
    obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod m
    have h1 : jHom (MinData.Valid.slLower K e) ∈ Jgrp K := by
      rw [← xu_theta]
      exact Subgroup.subset_closure ⟨e, Or.inl rfl⟩
    have h2 : jHom (MinData.Valid.slUpper K a) ∈ Jgrp K := by
      rw [← xu_neg_theta]
      exact Subgroup.subset_closure ⟨a, Or.inr rfl⟩
    have h3 : jHom (MinData.Valid.slLower K b) ∈ Jgrp K := by
      rw [← xu_theta]
      exact Subgroup.subset_closure ⟨b, Or.inl rfl⟩
    have h4 : jHom (MinData.Valid.slUpper K c) ∈ Jgrp K := by
      rw [← xu_neg_theta]
      exact Subgroup.subset_closure ⟨c, Or.inr rfl⟩
    rw [map_mul, map_mul, map_mul]
    exact mul_mem (mul_mem (mul_mem h1 h2) h3) h4

theorem Jgrp_le_E : Jgrp K ≤ EGrp K := by
  rw [Jgrp, Subgroup.closure_le]
  rintro g ⟨c, rfl | rfl⟩
  · exact e7Data_valid.xu_mem K theta c
  · exact e7Data_valid.xu_mem K (-theta) c

theorem J_fixes_V0 [CharP K 2] {j : (Module.End K (V K))ˣ} (hj : j ∈ Jgrp K) {v : V K}
    (hv : v ∈ V0 K) : (j : Module.End K (V K)) v = v := by
  rw [Jgrp_eq_range] at hj
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hj
  rw [mem_V0] at hv
  have hvb : ∀ b, pr b theta ≠ 0 → v b = 0 := fun b hb => hv b (fun h => hb (mem_idx0.1 h))
  rw [jHom_val]
  ext b
  rw [jOp_apply]
  unfold jFun
  rcases pr_mem isRoot_theta b with h | h | h
  · have h0 : pr b theta ≠ 0 := by rw [h]; norm_num
    have hs : pr (shift theta b) theta ≠ 0 := by rw [pr_shift_self isRoot_theta h]; norm_num
    rw [if_neg h0, if_pos h, hvb b h0, hvb (shift theta b) hs]
    ring
  · rw [if_pos h]
  · have h0 : pr b theta ≠ 0 := by rw [h]; norm_num
    have h1 : ¬ pr b theta = -1 := by rw [h]; norm_num
    have hs : pr (shift (-theta) b) theta ≠ 0 := by rw [pr_shift_neg isRoot_theta h]; norm_num
    rw [if_neg h0, if_neg h1, hvb b h0, hvb (shift (-theta) b) hs]
    ring

theorem fixed_eq_V0 [CharP K 2] {j : (Module.End K (V K))ˣ} (hj : j ∈ Jgrp K) (h1 : j ≠ 1)
    (ho : Odd (orderOf j)) :
    {v : V K | (j : Module.End K (V K)) v = v} = (V0 K : Set (V K)) := by
  have hj' := hj
  rw [Jgrp_eq_range] at hj'
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hj'
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, (m : Matrix (Fin 2) (Fin 2) K) = M :=
    ⟨_, rfl⟩
  have hjM : ∀ v : V K, (j : Module.End K (V K)) v = jOp M v := by
    intro v
    rw [← hm, jHom_val, hMdef]
  have hdet : M.det = 1 := by
    rw [← hMdef]
    exact Matrix.SpecialLinearGroup.det_coe m
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have htne : M 0 0 + M 1 1 ≠ 0 := by
    intro ht
    apply h1
    have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 := by
      linear_combination (-1 : K) * hdet + M 0 0 * ht - h2
    have e01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 := by
      linear_combination M 0 1 * ht
    have e10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
      linear_combination M 1 0 * ht
    have e11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = 1 := by
      linear_combination (-1 : K) * hdet + M 1 1 * ht - h2
    have hMM : M * M = 1 := by
      ext i k
      fin_cases i <;> fin_cases k
      · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e00
      · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e01
      · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e10
      · simpa [Matrix.mul_apply, Fin.sum_univ_two] using e11
    have hsq : j * j = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one, ← hm, jHom_val, hMdef, ← jOp_mul, hMM, jOp_one]
    have hpow : j ^ 2 = 1 := by rw [sq]; exact hsq
    have hdvd : orderOf j ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
    have hle : orderOf j ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have ho1 : orderOf j = 1 := by
      obtain ⟨k, hk⟩ := ho
      omega
    exact orderOf_eq_one_iff.mp ho1
  ext v
  constructor
  · intro hv
    have hv' : (j : Module.End K (V K)) v = v := hv
    rw [SetLike.mem_coe, mem_V0]
    have hJv : jOp M v = v := (hjM v).symm.trans hv'
    have hfix : ∀ b, jFun M ⇑v b = v b := by
      intro b
      rw [← jOp_apply, hJv]
    have hkey : ∀ b, pr b theta = -1 → v b = 0 ∧ v (shift theta b) = 0 := by
      intro b hb
      have hsh : pr (shift theta b) theta = 1 := pr_shift_self isRoot_theta hb
      have hsh' : shift (-theta) (shift theta b) = b := shift_neg_shift isRoot_theta hb
      have hb0 : pr b theta ≠ 0 := by rw [hb]; norm_num
      have hc0 : pr (shift theta b) theta ≠ 0 := by rw [hsh]; norm_num
      have hc1 : ¬ pr (shift theta b) theta = -1 := by rw [hsh]; norm_num
      have eq1 : M 0 0 * v b + M 0 1 * v (shift theta b) = v b := by
        have h := hfix b
        unfold jFun at h
        rw [if_neg hb0, if_pos hb] at h
        exact h
      have eq2 : M 1 0 * v b + M 1 1 * v (shift theta b) = v (shift theta b) := by
        have h := hfix (shift theta b)
        unfold jFun at h
        rw [if_neg hc0, if_neg hc1, hsh'] at h
        exact h
      have hD : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 = -(M 0 0 + M 1 1) := by
        linear_combination hdet + h2
      have hDne : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 ≠ 0 := by
        rw [hD]
        exact neg_ne_zero.mpr htne
      have hx : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * v b = 0 := by
        linear_combination (M 1 1 - 1) * eq1 - M 0 1 * eq2
      have hy : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * v (shift theta b) = 0 := by
        linear_combination (M 0 0 - 1) * eq2 - M 1 0 * eq1
      exact ⟨(mul_eq_zero.mp hx).resolve_left hDne, (mul_eq_zero.mp hy).resolve_left hDne⟩
    intro b hb
    rcases pr_mem isRoot_theta b with h | h | h
    · exact (hkey b h).1
    · exact absurd (mem_idx0.2 h) hb
    · have ha : pr (shift (-theta) b) theta = -1 := pr_shift_neg isRoot_theta h
      have h3 := (hkey (shift (-theta) b) ha).2
      rwa [shift_shift_neg isRoot_theta h] at h3
  · intro hv
    exact J_fixes_V0 hj (SetLike.mem_coe.mp hv)

@[expose] def IsRootElt (g : (Module.End K (V K))ˣ) : Prop :=
  ∃ h ∈ EGrp K, ∃ (γ : Fin (Tag.rank .E7) → ℤ) (c : K), IsRoot .E7 γ ∧ c ≠ 0 ∧
    g = h * e7Data_valid.xu K γ c * h⁻¹

theorem IsRootElt.sub_one_conj {g : (Module.End K (V K))ˣ} (hg : IsRootElt g) :
    ∃ (u u' : Module.End K (V K)) (γ : Fin (Tag.rank .E7) → ℤ) (c : K), IsRoot .E7 γ ∧ c ≠ 0 ∧
      u * u' = 1 ∧ u' * u = 1 ∧
      (g : Module.End K (V K)) - 1 = u * (c • e7Data.rootOp K γ) * u' := by
  obtain ⟨h, -, γ, c, hγ, hc, rfl⟩ := hg
  refine ⟨(h : Module.End K (V K)), ((h⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)), γ, c,
    hγ, hc, Units.mul_inv h, Units.inv_mul h, ?_⟩
  rw [Units.val_mul, Units.val_mul, e7Data_valid.xu_val]
  simp only [mul_add, mul_one, add_mul]
  rw [Units.mul_inv h]
  abel

theorem rootOp_range_eq_supported [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    LinearMap.range (e7Data.rootOp K γ) =
      Finsupp.supported K K ((Finset.univ.filter fun b : Fin e7Data.d => pr b γ = 1 :
        Finset (Fin e7Data.d)) : Set (Fin e7Data.d)) := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    rw [Finsupp.mem_supported']
    intro b hb
    have hb' : ¬ pr b γ = 1 := fun h =>
      hb (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
    rw [rootOp_apply hγ, if_neg hb']
  · intro w hw
    rw [Finsupp.mem_supported'] at hw
    refine ⟨Finsupp.equivFunOnFinite.symm (fun a => if pr a γ = -1 then w (shift γ a) else 0), ?_⟩
    ext b
    rw [rootOp_apply hγ]
    by_cases hb : pr b γ = 1
    · rw [if_pos hb]
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
      rw [if_pos (pr_shift_neg hγ hb), shift_shift_neg hγ hb]
    · rw [if_neg hb]
      have hb'' : b ∉ ((Finset.univ.filter fun b : Fin e7Data.d => pr b γ = 1 :
          Finset (Fin e7Data.d)) : Set (Fin e7Data.d)) :=
        fun h => hb (Finset.mem_filter.1 (Finset.mem_coe.1 h)).2
      exact (hw b hb'').symm

theorem IsRootElt.sub_one_sq [CharP K 2] {g : (Module.End K (V K))ˣ} (hg : IsRootElt g) :
    ((g : Module.End K (V K)) - 1) * ((g : Module.End K (V K)) - 1) = 0 := by
  obtain ⟨u, u', γ, c, -, -, hu, hu', he⟩ := IsRootElt.sub_one_conj hg
  have hXX : (c • e7Data.rootOp K γ) * (c • e7Data.rootOp K γ) = 0 := by
    rw [smul_mul_smul_comm, e7Data_valid.rootOp_mul_self, smul_zero]
  rw [he]
  calc u * (c • e7Data.rootOp K γ) * u' * (u * (c • e7Data.rootOp K γ) * u')
      = u * ((c • e7Data.rootOp K γ) * (u' * u) * (c • e7Data.rootOp K γ)) * u' := by
        simp only [mul_assoc]
    _ = u * ((c • e7Data.rootOp K γ) * (c • e7Data.rootOp K γ)) * u' := by
        rw [hu', mul_one]
    _ = 0 := by rw [hXX, mul_zero, zero_mul]

end CFSG.RankThree.GF2n.Smith81.E7Model
