module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLRoot

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix
open scoped LinearAlgebra.Projectivization

section Tv

variable {n : ℕ} {K : Type} [Field K]

@[expose] def tv (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0) : SpecialLinearGroup (Fin n) K :=
  ⟨1 + vecMulVec v φ, by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]⟩

theorem tv_coe (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0) :
    (tv v φ h : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec v φ := rfl

theorem matrix_add_self [CharP K 2] (M : Matrix (Fin n) (Fin n) K) : M + M = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem tv_mul_self [CharP K 2] (v φ : Fin n → K) (h : φ ⬝ᵥ v = 0) :
    tv v φ h * tv v φ h = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, tv_coe, Matrix.SpecialLinearGroup.coe_one]
  have hVV : vecMulVec v φ * vecMulVec v φ = 0 := by
    rw [vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]
  have e2 : (1 + vecMulVec v φ) * (1 + vecMulVec v φ) = 1 + (vecMulVec v φ + vecMulVec v φ) +
      vecMulVec v φ * vecMulVec v φ := by noncomm_ring
  rw [e2, matrix_add_self, hVV]
  simp

theorem tv_sq [CharP K 2] {v φ e ψ : Fin n → K} (hφ : φ ⬝ᵥ v = 0) (hψ : ψ ⬝ᵥ e = 0)
    (hψv : ψ ⬝ᵥ v = 0) :
    (tv e ψ hψ * tv v φ hφ) * (tv e ψ hψ * tv v φ hφ) =
      tv v ((φ ⬝ᵥ e) • ψ) (by rw [smul_dotProduct, hψv, smul_zero]) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, tv_coe]
  have hEE : vecMulVec e ψ * vecMulVec e ψ = 0 := by
    rw [vecMulVec_mul_vecMulVec, hψ, zero_smul, vecMulVec_zero]
  have hVV : vecMulVec v φ * vecMulVec v φ = 0 := by
    rw [vecMulVec_mul_vecMulVec, hφ, zero_smul, vecMulVec_zero]
  have hEV : vecMulVec e ψ * vecMulVec v φ = 0 := by
    rw [vecMulVec_mul_vecMulVec, hψv, zero_smul, vecMulVec_zero]
  have hVE : vecMulVec v φ * vecMulVec e ψ = vecMulVec v ((φ ⬝ᵥ e) • ψ) :=
    vecMulVec_mul_vecMulVec _ _ _ _
  have e1 : (1 + vecMulVec e ψ) * (1 + vecMulVec v φ) = 1 + vecMulVec e ψ + vecMulVec v φ := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hEV, add_zero]
    abel
  have e2 : (1 + vecMulVec e ψ + vecMulVec v φ) * (1 + vecMulVec e ψ + vecMulVec v φ) =
      1 + (vecMulVec e ψ + vecMulVec e ψ) + (vecMulVec v φ + vecMulVec v φ) +
        (vecMulVec e ψ * vecMulVec e ψ + vecMulVec e ψ * vecMulVec v φ +
          vecMulVec v φ * vecMulVec e ψ + vecMulVec v φ * vecMulVec v φ) := by
    noncomm_ring
  rw [e1, e2, matrix_add_self (vecMulVec e ψ), matrix_add_self (vecMulVec v φ), hEE, hEV, hVE,
    hVV]
  simp

theorem coe_inv_mul_self (g : SpecialLinearGroup (Fin n) K) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_self_mul_inv (g : SpecialLinearGroup (Fin n) K) :
    (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem dot_conj (g : SpecialLinearGroup (Fin n) K) (v φ : Fin n → K) :
    (φ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⬝ᵥ
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = φ ⬝ᵥ v := by
  rw [dotProduct_mulVec, vecMul_vecMul, coe_inv_mul_self, vecMul_one]

theorem conj_tv (g : SpecialLinearGroup (Fin n) K) {v φ : Fin n → K} (h : φ ⬝ᵥ v = 0) :
    g * tv v φ h * g⁻¹ = tv ((g : Matrix (Fin n) (Fin n) K) *ᵥ v)
      (φ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (by rw [dot_conj, h]) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, tv_coe, tv_coe,
    mul_add, add_mul,
    mul_one, mul_vecMulVec, vecMulVec_mul, coe_self_mul_inv]

theorem tv_smul {v φ : Fin n → K} (c : K) (h : φ ⬝ᵥ v = 0) :
    tv (c • v) φ (by rw [dotProduct_smul, h, smul_zero]) = tv v (c • φ)
      (by rw [smul_dotProduct, h, smul_zero]) := by
  apply Subtype.ext
  rw [tv_coe, tv_coe, smul_vecMulVec, vecMulVec_smul]

theorem tv_mem_slSub {k : Subfield K} {v φ : Fin n → K} (h : φ ⬝ᵥ v = 0) (hv : ∀ i, v i ∈ k)
    (hφ : ∀ i, φ i ∈ k) : tv v φ h ∈ slSub n k := by
  rw [mem_slSub]
  intro i j
  rw [tv_coe, Matrix.add_apply, vecMulVec_apply, Matrix.one_apply]
  refine k.add_mem ?_ (k.mul_mem (hv i) (hφ j))
  split_ifs
  · exact k.one_mem
  · exact k.zero_mem

theorem tv_eq_of_eq {v v' φ φ' : Fin n → K} (hv : v = v') (hφ : φ = φ') (h : φ ⬝ᵥ v = 0)
    (h' : φ' ⬝ᵥ v' = 0) : tv v φ h = tv v' φ' h' := by
  subst hv hφ
  rfl

theorem transvection_eq_tv {i j : Fin n} (hij : i ≠ j) (a : K) :
    SpecialLinearGroup.transvection hij a = tv (Pi.single i 1) (a • Pi.single j 1)
      (by simp [dotProduct_single, hij]) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe, tv_coe]
  congr 1
  ext p q
  simp only [Matrix.single_apply, vecMulVec_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h1 : p = i
  · by_cases h2 : q = j
    · subst h1 h2
      simp
    · have h2' : ¬ j = q := fun h => h2 h.symm
      simp [h1, h2, h2']
  · have : ¬ (i = p ∧ j = q) := fun h => h1 h.1.symm
    simp [h1, this]

@[expose] def dualHom : SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K where
  toFun x := Matrix.SpecialLinearGroup.transpose x⁻¹
  map_one' := Subtype.ext (by simp [Matrix.SpecialLinearGroup.transpose])
  map_mul' x y := Subtype.ext (by
    simp only [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul])

theorem coe_dualHom (x : SpecialLinearGroup (Fin n) K) :
    ((dualHom x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl

theorem dualHom_dualHom (x : SpecialLinearGroup (Fin n) K) : dualHom (dualHom x) = x := by
  set y := dualHom x with hy
  have h1 : y * Matrix.SpecialLinearGroup.transpose x = 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, hy, coe_dualHom, Matrix.SpecialLinearGroup.coe_transpose,
      ← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have h2 : y⁻¹ = Matrix.SpecialLinearGroup.transpose x := inv_eq_of_mul_eq_one_right h1
  show Matrix.SpecialLinearGroup.transpose y⁻¹ = x
  rw [h2]
  exact Subtype.ext (by simp [Matrix.SpecialLinearGroup.transpose])

theorem dualHom_tv [CharP K 2] (v ψ : Fin n → K) (h : ψ ⬝ᵥ v = 0) :
    dualHom (tv v ψ h) = tv ψ v (by rw [dotProduct_comm]; exact h) := by
  have hinv : (tv v ψ h)⁻¹ = tv v ψ h := inv_eq_of_mul_eq_one_right (tv_mul_self v ψ h)
  apply Subtype.ext
  show ((tv v ψ h)⁻¹ : SpecialLinearGroup (Fin n) K).1ᵀ = _
  rw [hinv, tv_coe, tv_coe, transpose_add, transpose_one, transpose_vecMulVec]

theorem dualHom_mem_slSub {k : Subfield K} {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ slSub n k) : dualHom x ∈ slSub n k := by
  rw [mem_slSub] at hx ⊢
  intro i j
  rw [coe_dualHom, transpose_apply]
  exact (mem_slSub.mp ((slSub n k).inv_mem (mem_slSub.mpr hx))) j i

theorem dualHom_transvection [CharP K 2] {i j : Fin n} (hij : i ≠ j) (a : K) :
    dualHom (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm a := by
  rw [transvection_eq_tv hij a, dualHom_tv, transvection_eq_tv hij.symm a]
  exact tv_smul a (by simp [hij])

end Tv

section Rational

variable {n : ℕ} {K : Type} [Field K] {k : Subfield K}

theorem exists_slSub_mulVec_eq_smul_single {e : Fin n → K} (he : ∀ i, e i ∈ k) (he0 : e ≠ 0)
    (i₀ : Fin n) :
    ∃ g ∈ slSub n k, ∃ c ∈ k, c ≠ 0 ∧
      (g : Matrix (Fin n) (Fin n) K) *ᵥ e = c • Pi.single i₀ 1 := by
  let e' : Fin n → k := fun i => ⟨e i, he i⟩
  have he' : e' ≠ 0 := by
    intro h
    apply he0
    funext i
    simpa [e'] using congrArg Subtype.val (congrFun h i)
  let w : Fin n → k := Pi.single i₀ 1
  have hw : w ≠ 0 := by
    intro h
    simpa [w] using congrFun h i₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin n) k)
    (Projectivization.mk k e' he') (Projectivization.mk k w hw)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hg
  obtain ⟨c, hc⟩ := hg
  refine ⟨Matrix.SpecialLinearGroup.map k.subtype g, ⟨g, rfl⟩, (c : k), (c : k).2, ?_, ?_⟩
  · exact fun h => c.ne_zero (Subtype.ext h)
  · ext i
    have hc' : c • w = (g : Matrix (Fin n) (Fin n) k) *ᵥ e' := hc
    have h2 := RingHom.map_mulVec k.subtype (g : Matrix (Fin n) (Fin n) k) e' i
    rw [← hc'] at h2
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    have h3 : (k.subtype ∘ e') = e := funext fun _ => rfl
    rw [h3] at h2
    simp only [Pi.smul_apply, smul_eq_mul, Units.smul_def] at h2 ⊢
    rw [RingHom.mapMatrix_apply, ← h2, map_mul]
    by_cases hi : i = i₀ <;> simp [w, hi]

variable {H : Subgroup (SpecialLinearGroup (Fin n) K)}

theorem tv_mem_congr {v φ φ' : Fin n → K} (hφ : φ = φ') (h : φ ⬝ᵥ v = 0) (h' : φ' ⬝ᵥ v = 0)
    (hm : tv v φ h ∈ H) : tv v φ' h' ∈ H := by
  subst hφ
  exact hm

theorem root_mem_of_tv_single [CharP K 2] (hk : slSub n k ≤ H) (hn : 3 ≤ n) {i₀ : Fin n}
    {γ : Fin n → K} (hγ : γ ⬝ᵥ Pi.single i₀ 1 = 0) (hmem : tv (Pi.single i₀ 1) γ hγ ∈ H)
    (j : Fin n) :
    ∃ l, ∃ hl : i₀ ≠ l, SpecialLinearGroup.transvection hl (γ j) ∈ H := by
  obtain ⟨l, hl1, hl2⟩ := exists_fin_ne_ne' hn i₀ j
  refine ⟨l, hl1.symm, ?_⟩
  have hjl : j ≠ l := hl2.symm
  have hψ : (Pi.single l 1 : Fin n → K) ⬝ᵥ Pi.single j 1 = 0 := by simp [hl2]
  have hψv : (Pi.single l 1 : Fin n → K) ⬝ᵥ Pi.single i₀ 1 = 0 := by simp [hl1]
  have hs : tv (Pi.single j 1) (Pi.single l 1) hψ ∈ H := by
    have h0 : SpecialLinearGroup.transvection hjl (1 : K) ∈ H :=
      hk (transvection_mem_slSub hjl k.one_mem)
    rw [transvection_eq_tv hjl 1] at h0
    exact tv_mem_congr (one_smul K _) _ hψ h0
  have h1 := H.mul_mem (H.mul_mem hs hmem) (H.mul_mem hs hmem)
  rw [tv_sq hγ hψ hψv] at h1
  rw [transvection_eq_tv hl1.symm (γ j)]
  exact tv_mem_congr (by rw [dotProduct_single_one]) _ _ h1

theorem rat_axis_of_rat_center [CharP K 2] (hk : slSub n k ≤ H) (hn : 3 ≤ n)
    (NIR : ∀ a ∉ k, ∀ (i j : Fin n) (hij : i ≠ j), SpecialLinearGroup.transvection hij a ∉ H)
    {e γ : Fin n → K} (he : ∀ i, e i ∈ k) (he0 : e ≠ 0) (hγ : γ ⬝ᵥ e = 0)
    (hmem : tv e γ hγ ∈ H) : ∀ i, γ i ∈ k := by
  let i₀ : Fin n := ⟨0, by omega⟩
  obtain ⟨g, hgk, c, hck, hc0, hge⟩ := exists_slSub_mulVec_eq_smul_single he he0 i₀
  have hconj : g * tv e γ hγ * g⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (hk hgk) hmem) (H.inv_mem (hk hgk))
  rw [conj_tv g hγ] at hconj
  set φ₁ : Fin n → K := γ ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hφ₁
  have hd := dot_conj g e γ
  rw [hge, dotProduct_smul, hγ, smul_eq_mul] at hd
  have hφ1 : φ₁ ⬝ᵥ (Pi.single i₀ 1 : Fin n → K) = 0 := (mul_eq_zero.mp hd).resolve_left hc0
  have hγ'e : (c • φ₁) ⬝ᵥ (Pi.single i₀ 1 : Fin n → K) = 0 := by
    rw [smul_dotProduct, hφ1, smul_zero]
  have h1 : tv (Pi.single i₀ 1) (c • φ₁) hγ'e ∈ H := by
    have heq : tv ((g : Matrix (Fin n) (Fin n) K) *ᵥ e) φ₁ (by rw [hφ₁, dot_conj, hγ]) =
        tv (Pi.single i₀ 1) (c • φ₁) hγ'e :=
      (tv_eq_of_eq hge rfl _ (by rw [dotProduct_smul, hφ1, smul_zero])).trans (tv_smul c hφ1)
    exact heq ▸ hconj
  have hrat : ∀ j, (c • φ₁) j ∈ k := by
    intro j
    by_contra hj
    obtain ⟨l, hl, hroot⟩ := root_mem_of_tv_single hk hn hγ'e h1 j
    exact NIR _ hj i₀ l hl hroot
  have hγeq : (c • φ₁) ᵥ* ((g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • γ := by
    rw [smul_vecMul, hφ₁, vecMul_vecMul, coe_inv_mul_self, vecMul_one]
  intro j
  have hcj : c * γ j ∈ k := by
    have h2 := congrFun hγeq j
    rw [Pi.smul_apply, smul_eq_mul] at h2
    rw [← h2, Matrix.vecMul, dotProduct]
    exact k.sum_mem fun i _ => k.mul_mem (hrat i) ((mem_slSub.mp hgk) i j)
  have : γ j = c⁻¹ * (c * γ j) := by field_simp
  rw [this]
  exact k.mul_mem (k.inv_mem hck) hcj

theorem rat_center_of_rat_axis [CharP K 2] (hk : slSub n k ≤ H) (hn : 3 ≤ n)
    (NIR : ∀ a ∉ k, ∀ (i j : Fin n) (hij : i ≠ j), SpecialLinearGroup.transvection hij a ∉ H)
    {v ψ : Fin n → K} (hψ : ∀ i, ψ i ∈ k) (hψ0 : ψ ≠ 0) (h : ψ ⬝ᵥ v = 0)
    (hmem : tv v ψ h ∈ H) : ∀ i, v i ∈ k := by
  have hk' : slSub n k ≤ H.map dualHom := fun x hx =>
    ⟨dualHom x, hk (dualHom_mem_slSub hx), dualHom_dualHom x⟩
  have NIR' : ∀ a ∉ k, ∀ (i j : Fin n) (hij : i ≠ j),
      SpecialLinearGroup.transvection hij a ∉ H.map dualHom := by
    intro a ha i j hij hmem'
    obtain ⟨y, hy, hyx⟩ := hmem'
    apply NIR a ha j i hij.symm
    have hy' : y = dualHom (SpecialLinearGroup.transvection hij a) := by
      rw [← hyx, dualHom_dualHom]
    rw [hy', dualHom_transvection hij a] at hy
    exact hy
  exact rat_axis_of_rat_center hk' hn NIR' hψ hψ0 (by rw [dotProduct_comm]; exact h)
    ⟨tv v ψ h, hmem, dualHom_tv v ψ h⟩

end Rational

end CFSG.RankThree.PartOne.CTP
