module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly Matrix

variable {K : Type} [Field K]

section Dim

variable [Finite K] (hK : Nat.card K = 4)

theorem cube_sum_of_unit_ne_one {lam : Kˣ} (hlam3 : lam ^ 3 = 1) (hlamne : lam ≠ 1) :
    (lam : K) ^ 2 + (lam : K) + 1 = 0 := by
  have hval : (lam : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hlam3]; rfl
  have hfac : ((lam : K) - 1) * ((lam : K) ^ 2 + (lam : K) + 1) = 0 := by
    linear_combination hval
  rcases mul_eq_zero.mp hfac with h | h
  · exfalso
    apply hlamne
    exact Units.ext (sub_eq_zero.mp h)
  · exact h

theorem lam_sq_ne_one (hK : Nat.card K = 4) {lam : Kˣ}
    (hlamsum : (lam : K) ^ 2 + (lam : K) + 1 = 0) :
    (lam : K) ^ 2 ≠ 1 := by
  intro h
  have htwo := two_eq_zero hK
  have hzero : (lam : K) = 0 := by
    linear_combination hlamsum - h - htwo
  exact lam.ne_zero hzero

theorem lam_ne_sq {lam : Kˣ} (hlamne : lam ≠ 1) : (lam : K) ≠ (lam : K) ^ 2 := by
  intro h
  have h' : (lam : K) * 1 = (lam : K) * (lam : K) := by
    rw [mul_one]
    simpa [pow_two] using h
  have h1 : (1 : K) = (lam : K) := mul_left_cancel₀ lam.ne_zero h'
  exact hlamne (Units.ext h1.symm)

theorem lam_val_ne_one {lam : Kˣ} (hlamne : lam ≠ 1) : (lam : K) ≠ 1 := by
  intro h
  exact hlamne (Units.ext h)

theorem cube_eigen_decomposition (hK : Nat.card K = 4)
    {M : Matrix (Fin 6) (Fin 6) K} (hM3 : M ^ 3 = 1)
    {lam : Kˣ} (hlam3 : lam ^ 3 = 1) (hlamne : lam ≠ 1) :
    ∀ v : Fin 6 → K, ∃ v0 ∈ Module.End.eigenspace (Matrix.toLin' M) (1 : K),
      ∃ v1 ∈ Module.End.eigenspace (Matrix.toLin' M) ((lam : K)),
      ∃ v2 ∈ Module.End.eigenspace (Matrix.toLin' M) ((lam : K) ^ 2), v = v0 + v1 + v2 := by
  classical
  haveI : FiniteDimensional K (Fin 6 → K) := FiniteDimensional.finiteDimensional_pi K
  have hlamval3 : (lam : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hlam3]; rfl
  have hlamsum : (lam : K) ^ 2 + (lam : K) + 1 = 0 :=
    cube_sum_of_unit_ne_one hlam3 hlamne
  let f : Module.End K (Fin 6 → K) := Matrix.toLin' M
  let e : Fin 3 → K := ![1, (lam : K), (lam : K) ^ 2]
  have he2 : e 2 = (lam : K) ^ 2 := by simp [e]
  have hf3 : f ^ 3 = 1 := by
    dsimp [f]
    rw [← Matrix.toLin'_pow, hM3, Matrix.toLin'_one]
    exact Module.End.one_eq_id.symm
  have hf3v : ∀ v : (Fin 6 → K), f (f (f v)) = v := by
    intro v
    have h := congrFun (congrArg (fun g : Module.End K (Fin 6 → K) =>
      (g : (Fin 6 → K) → (Fin 6 → K))) hf3) v
    simpa [pow_succ, Module.End.mul_apply] using h
  let P : K → Module.End K (Fin 6 → K) := fun mu => 1 + mu ^ 2 • f + mu • f ^ 2
  have hP : ∀ mu, mu ^ 3 = 1 → f * P mu = mu • P mu := by
    intro mu hmu
    apply LinearMap.ext
    intro v
    simp only [P, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [map_add, map_add, map_smul, map_smul]
    simp only [pow_two, Module.End.mul_apply, hf3v, smul_add, smul_smul]
    have h3 : mu * (mu * mu) = 1 := by
      calc mu * (mu * mu) = mu ^ 3 := by ring
        _ = 1 := hmu
    have h2 : mu * mu = mu ^ 2 := by ring
    rw [h3, h2, one_smul]
    abel
  have hPmem : ∀ mu, mu ^ 3 = 1 → ∀ v : (Fin 6 → K), P mu v ∈ f.eigenspace mu := by
    intro mu hmu v
    rw [Module.End.mem_eigenspace_iff]
    have h := congrFun (congrArg (fun g : Module.End K (Fin 6 → K) =>
      (g : (Fin 6 → K) → (Fin 6 → K))) (hP mu hmu)) v
    simpa [Module.End.mul_apply] using h
  have he3 : ∀ i, e i ^ 3 = 1 := by
    intro i
    fin_cases i
    · simp [e]
    · simpa [e] using hlamval3
    · change ((lam : K) ^ 2) ^ 3 = 1
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hlamval3, one_pow]
  have hsumP : P (e 0) + P (e 1) + P (e 2) = 1 := by
    have hsq : ((lam : K) ^ 2) ^ 2 = (lam : K) := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hlamval3, one_mul]
    have hthree : (1 : K) + 1 + 1 = 1 := by
      calc (1 : K) + 1 + 1 = ((1 : K) + 1) + 1 := by ring
        _ = 0 + 1 := by rw [one_add_one_eq_zero hK]
        _ = 1 := zero_add 1
    have hc1 : (1 : K) + (lam : K) ^ 2 + (lam : K) = 0 := by
      linear_combination hlamsum
    have hc2 : (1 : K) + (lam : K) + (lam : K) ^ 2 = 0 := by
      linear_combination hlamsum
    apply LinearMap.ext
    intro v
    simp only [P, e, he2, hsq, hthree, hc1, hc2, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, one_pow, one_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    have hx : f v + (lam : K) ^ 2 • f v + (lam : K) • f v = 0 := by
      rw [← one_smul K (f v)]
      simp only [smul_smul, one_mul, mul_one]
      rw [← add_smul, ← add_smul, hc1, zero_smul]
    have hy : (f ^ 2) v + (lam : K) • (f ^ 2) v + (lam : K) ^ 2 • (f ^ 2) v = 0 := by
      rw [← one_smul K ((f ^ 2) v)]
      simp only [smul_smul, one_mul, mul_one]
      rw [← add_smul, ← add_smul, hc2, zero_smul]
    have hv : v + v + v = v := by
      rw [← one_smul K v]
      rw [← add_smul, ← add_smul, hthree, one_smul]
    calc
      v + f v + (f ^ 2) v + (v + (lam : K) ^ 2 • f v + (lam : K) • (f ^ 2) v) +
          (v + (lam : K) • f v + (lam : K) ^ 2 • (f ^ 2) v)
          = (v + v + v) + (f v + (lam : K) ^ 2 • f v + (lam : K) • f v) +
              ((f ^ 2) v + (lam : K) • (f ^ 2) v + (lam : K) ^ 2 • (f ^ 2) v) := by
            abel
      _ = v + 0 + 0 := by rw [hv, hx, hy]
      _ = v := by simp
  have hdecomp : ∀ v : (Fin 6 → K), v = P (e 0) v + P (e 1) v + P (e 2) v := by
    intro v
    have h := congrFun (congrArg (fun g : Module.End K (Fin 6 → K) =>
      (g : (Fin 6 → K) → (Fin 6 → K))) hsumP) v
    simpa [Module.End.mul_apply] using h.symm
  intro v
  refine ⟨P (e 0) v, ?_, P (e 1) v, ?_, P (e 2) v, ?_, hdecomp v⟩
  · change P (e 0) v ∈ f.eigenspace (e 0)
    exact hPmem (e 0) (he3 0) v
  · change P (e 1) v ∈ f.eigenspace (e 1)
    exact hPmem (e 1) (he3 1) v
  · rw [← he2]
    change P (e 2) v ∈ f.eigenspace (e 2)
    exact hPmem (e 2) (he3 2) v

theorem dim_eigenspace_one_eq_two (hK : Nat.card K = 4)
    {M C : Matrix (Fin 6) (Fin 6) K} (hM3 : M ^ 3 = 1)
    {lam : Kˣ} (hlam3 : lam ^ 3 = 1) (hlamne : lam ≠ 1)
    (hrel : M * C = Matrix.scalar (Fin 6) (((lam⁻¹ : Kˣ) : K)) * C * M)
    (hCdet : IsUnit C.det) :
    Module.finrank K (Module.End.eigenspace (Matrix.toLin' M) (1 : K)) = 2 := by
  classical
  haveI : FiniteDimensional K (Fin 6 → K) := FiniteDimensional.finiteDimensional_pi K
  have hlamval3 : (lam : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hlam3]; rfl
  have hlamsum : (lam : K) ^ 2 + (lam : K) + 1 = 0 :=
    cube_sum_of_unit_ne_one hlam3 hlamne
  have hlam2ne1 : (lam : K) ^ 2 ≠ 1 := lam_sq_ne_one hK hlamsum
  have hlamnesq : (lam : K) ≠ (lam : K) ^ 2 := lam_ne_sq hlamne
  have hlam_inv : lam⁻¹ = lam ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    calc lam * lam ^ 2 = lam ^ (1 + 2) := by simpa using (pow_add lam 1 2).symm
      _ = lam ^ 3 := by norm_num
      _ = 1 := hlam3
  have hlam_inv_val : (lam : K)⁻¹ = (lam : K) ^ 2 := by
    rw [← Units.val_inv_eq_inv_val, hlam_inv]
    rfl
  have hlamvalne : (lam : K) ≠ 1 := lam_val_ne_one hlamne
  let f : Module.End K (Fin 6 → K) := Matrix.toLin' M
  let e : Fin 3 → K := ![1, (lam : K), (lam : K) ^ 2]
  have he2 : e 2 = (lam : K) ^ 2 := by simp [e]
  let V : Fin 3 → Submodule K (Fin 6 → K) := fun i => f.eigenspace (e i)
  have hf3 : f ^ 3 = 1 := by
    dsimp [f]
    rw [← Matrix.toLin'_pow, hM3, Matrix.toLin'_one]
    exact Module.End.one_eq_id.symm
  have hf3v : ∀ v : (Fin 6 → K), f (f (f v)) = v := by
    intro v
    have h := congrFun (congrArg
      (fun g : Module.End K (Fin 6 → K) => (g : (Fin 6 → K) → (Fin 6 → K))) hf3) v
    simpa [pow_succ, Module.End.mul_apply] using h
  let P : K → Module.End K (Fin 6 → K) := fun mu => 1 + mu ^ 2 • f + mu • f ^ 2
  have hP : ∀ mu, mu ^ 3 = 1 → f * P mu = mu • P mu := by
    intro mu hmu
    apply LinearMap.ext
    intro v
    simp only [P, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [map_add, map_add, map_smul, map_smul]
    simp only [pow_two, Module.End.mul_apply, hf3v, smul_add, smul_smul]
    have h3 : mu * (mu * mu) = 1 := by
      calc mu * (mu * mu) = mu ^ 3 := by ring
        _ = 1 := hmu
    have h2 : mu * mu = mu ^ 2 := by ring
    rw [h3, h2, one_smul]
    abel
  have hPmem : ∀ mu, mu ^ 3 = 1 → ∀ v : (Fin 6 → K), P mu v ∈ f.eigenspace mu := by
    intro mu hmu v
    rw [Module.End.mem_eigenspace_iff]
    have h := congrFun (congrArg
      (fun g : Module.End K (Fin 6 → K) => (g : (Fin 6 → K) → (Fin 6 → K))) (hP mu hmu)) v
    simpa [Module.End.mul_apply] using h
  have he3 : ∀ i, e i ^ 3 = 1 := by
    intro i
    fin_cases i
    · simp [e]
    · simpa [e] using hlamval3
    · change ((lam : K) ^ 2) ^ 3 = 1
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hlamval3, one_pow]
  have he_inj : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [e, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons] at hij
    · rfl
    · exact absurd hij.symm hlamvalne
    · exact absurd hij.symm hlam2ne1
    · exact absurd hij hlamvalne
    · rfl
    · exact absurd hij hlamnesq
    · exact absurd hij hlam2ne1
    · exact absurd hij.symm hlamnesq
    · rfl
  have hsumP : P (e 0) + P (e 1) + P (e 2) = 1 := by
    have hsq : ((lam : K) ^ 2) ^ 2 = (lam : K) := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hlamval3, one_mul]
    have hthree : (1 : K) + 1 + 1 = 1 := by
      calc (1 : K) + 1 + 1 = ((1 : K) + 1) + 1 := by ring
        _ = 0 + 1 := by rw [one_add_one_eq_zero hK]
        _ = 1 := zero_add 1
    have hc1 : (1 : K) + (lam : K) ^ 2 + (lam : K) = 0 := by
      linear_combination hlamsum
    have hc2 : (1 : K) + (lam : K) + (lam : K) ^ 2 = 0 := by
      linear_combination hlamsum
    apply LinearMap.ext
    intro v
    simp only [P, e, he2, hsq, hthree, hc1, hc2, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, one_pow, one_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    have hx : f v + (lam : K) ^ 2 • f v + (lam : K) • f v = 0 := by
      rw [← one_smul K (f v)]
      simp only [smul_smul, one_mul, mul_one]
      rw [← add_smul, ← add_smul, hc1, zero_smul]
    have hy : (f ^ 2) v + (lam : K) • (f ^ 2) v + (lam : K) ^ 2 • (f ^ 2) v = 0 := by
      rw [← one_smul K ((f ^ 2) v)]
      simp only [smul_smul, one_mul, mul_one]
      rw [← add_smul, ← add_smul, hc2, zero_smul]
    have hv : v + v + v = v := by
      rw [← one_smul K v]
      rw [← add_smul, ← add_smul, hthree, one_smul]
    calc
      v + f v + (f ^ 2) v + (v + (lam : K) ^ 2 • f v + (lam : K) • (f ^ 2) v) +
          (v + (lam : K) • f v + (lam : K) ^ 2 • (f ^ 2) v)
          = (v + v + v) + (f v + (lam : K) ^ 2 • f v + (lam : K) • f v) +
              ((f ^ 2) v + (lam : K) • (f ^ 2) v + (lam : K) ^ 2 • (f ^ 2) v) := by
            abel
      _ = v + 0 + 0 := by rw [hv, hx, hy]
      _ = v := by simp
  have hdecomp : ∀ v : (Fin 6 → K), v = P (e 0) v + P (e 1) v + P (e 2) v := by
    intro v
    have h := congrFun (congrArg
      (fun g : Module.End K (Fin 6 → K) => (g : (Fin 6 → K) → (Fin 6 → K))) hsumP) v
    simpa [Module.End.mul_apply] using h.symm
  have hspan : (⨆ i, V i) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [iSup_fin_three]
    refine (hdecomp v).symm ▸ ?_
    exact Submodule.add_mem_sup
      (Submodule.add_mem_sup (hPmem (e 0) (he3 0) v) (hPmem (e 1) (he3 1) v))
      (hPmem (e 2) (he3 2) v)
  have hind : iSupIndep V :=
    (Module.End.eigenspaces_iSupIndep f).comp he_inj
  have hdis := iSupIndep_fin_three.mp hind
  have hdis01 : Disjoint (V 0) (V 1) := hdis.1.mono_right le_sup_left
  have hdis2 : Disjoint (V 2) (V 0 ⊔ V 1) := hdis.2.2
  have h01 : Module.finrank K ↑(V 0 ⊔ V 1) = Module.finrank K (V 0) + Module.finrank K (V 1) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (V 0) (V 1)
    rw [hdis01.eq_bot, finrank_bot, add_zero] at h
    exact h
  have h012 : Module.finrank K ↑((V 0 ⊔ V 1) ⊔ V 2) =
      Module.finrank K ↑(V 0 ⊔ V 1) + Module.finrank K (V 2) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (V 0 ⊔ V 1) (V 2)
    rw [inf_comm, hdis2.eq_bot, finrank_bot, add_zero] at h
    exact h
  have htop : (V 0 ⊔ V 1 ⊔ V 2) = ⊤ := by
    rw [← iSup_fin_three]; exact hspan
  have htotal : Module.finrank K (Fin 6 → K) = 6 := by
    exact Module.finrank_fin_fun (R := K) (n := 6)
  have hdim3 : Module.finrank K (V 0) + Module.finrank K (V 1) + Module.finrank K (V 2) = 6 := by
    have h := h012
    rw [h01] at h
    rw [htop, finrank_top, htotal] at h
    omega
  let gC : (Fin 6 → K) ≃ₗ[K] (Fin 6 → K) :=
    { toFun := Matrix.toLin' C
      map_add' := fun x y => map_add (Matrix.toLin' C) x y
      map_smul' := fun a x => map_smul (Matrix.toLin' C) a x
      invFun := Matrix.toLin' C⁻¹
      left_inv := by
        intro v
        rw [← Matrix.toLin'_mul_apply, Matrix.nonsing_inv_mul C hCdet, Matrix.toLin'_one]
        rfl
      right_inv := by
        intro v
        rw [← Matrix.toLin'_mul_apply, Matrix.mul_nonsing_inv C hCdet, Matrix.toLin'_one]
        rfl }
  have htoLin_scalar : ∀ a : K,
      Matrix.toLin' (Matrix.scalar (Fin 6) a) = a • (1 : Module.End K (Fin 6 → K)) := by
    intro a
    apply LinearMap.ext
    intro v
    ext i
    simp [Matrix.toLin'_apply', Matrix.mulVec, Matrix.scalar_apply, Finset.sum_ite_eq']
  have hmap_mul : ∀ (mu : K) (w : (Fin 6 → K)), f w = mu • w →
      f (gC w) = ((lam : K)⁻¹ * mu) • gC w := by
    intro mu w hw
    change (Matrix.toLin' M) (Matrix.toLin' C w) =
      ((lam : K)⁻¹ * mu) • Matrix.toLin' C w
    rw [← Matrix.toLin'_mul_apply, hrel]
    rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply]
    rw [htoLin_scalar]
    simp only [LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply]
    rw [hw]
    rw [map_smul, smul_smul, Units.val_inv_eq_inv_val]
  have hmap0 : Submodule.map gC.toLinearMap (V 0) ≤ V 2 := by
    rintro w ⟨v, hv, rfl⟩
    change v ∈ f.eigenspace (e 0) at hv
    change gC v ∈ f.eigenspace (e 2)
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : f v = (1 : K) • v := by simpa [e] using hv
    have h := hmap_mul (1 : K) v (by simpa using hv')
    simpa [V, e, hlam_inv_val] using h
  have hlam_coef2 : (lam : K)⁻¹ * (lam : K) ^ 2 = (lam : K) := by
    rw [hlam_inv_val]
    calc (lam : K) ^ 2 * (lam : K) ^ 2 = (lam : K) ^ 4 := by ring
      _ = (lam : K) ^ 3 * (lam : K) := by ring
      _ = 1 * (lam : K) := by rw [hlamval3]
      _ = (lam : K) := one_mul _
  have hmap2 : Submodule.map gC.toLinearMap (V 2) ≤ V 1 := by
    rintro w ⟨v, hv, rfl⟩
    change v ∈ f.eigenspace (e 2) at hv
    change gC v ∈ f.eigenspace (e 1)
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : f v = (lam : K) ^ 2 • v := by simpa [e, he2] using hv
    have h := hmap_mul ((lam : K) ^ 2) v (by simpa using hv')
    simpa [V, e, hlam_coef2] using h
  have hlam_coef1 : (lam : K)⁻¹ * (lam : K) = 1 := by
    rw [hlam_inv_val]
    calc (lam : K) ^ 2 * (lam : K) = (lam : K) ^ 3 := by ring
      _ = 1 := hlamval3
  have hmap1 : Submodule.map gC.toLinearMap (V 1) ≤ V 0 := by
    rintro w ⟨v, hv, rfl⟩
    change v ∈ f.eigenspace (e 1) at hv
    change gC v ∈ f.eigenspace (e 0)
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : f v = (lam : K) • v := by simpa [e] using hv
    have h := hmap_mul ((lam : K)) v (by simpa using hv')
    simpa [V, e, hlam_coef1] using h
  have hle02 : Module.finrank K (V 0) ≤ Module.finrank K (V 2) := by
    calc Module.finrank K (V 0) = Module.finrank K ↑(Submodule.map gC.toLinearMap (V 0)) :=
          (LinearEquiv.finrank_map_eq gC (V 0)).symm
      _ ≤ Module.finrank K (V 2) := Submodule.finrank_mono hmap0
  have hle21 : Module.finrank K (V 2) ≤ Module.finrank K (V 1) := by
    calc Module.finrank K (V 2) = Module.finrank K ↑(Submodule.map gC.toLinearMap (V 2)) :=
          (LinearEquiv.finrank_map_eq gC (V 2)).symm
      _ ≤ Module.finrank K (V 1) := Submodule.finrank_mono hmap2
  have hle10 : Module.finrank K (V 1) ≤ Module.finrank K (V 0) := by
    calc Module.finrank K (V 1) = Module.finrank K ↑(Submodule.map gC.toLinearMap (V 1)) :=
          (LinearEquiv.finrank_map_eq gC (V 1)).symm
      _ ≤ Module.finrank K (V 0) := Submodule.finrank_mono hmap1
  have hd0 : Module.finrank K (V 0) = 2 := by omega
  exact hd0

end Dim

section Card

variable [Finite K]

theorem card_le_nine_of_matrix_data (hK : Nat.card K = 4)
    {M C : Matrix (Fin 6) (Fin 6) K} (hM3 : M ^ 3 = 1)
    {lam : Kˣ} (hlam3 : lam ^ 3 = 1) (hlamne : lam ≠ 1)
    (hrel : M * C = Matrix.scalar (Fin 6) (((lam⁻¹ : Kˣ) : K)) * C * M)
    (hCdet : IsUnit C.det) {R : Subgroup (GL (Fin 6) K)} (hR : IsPGroup 3 R)
    (hcomm : ∀ r ∈ R, (((r : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * M =
        M * (((r : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) ∧
      (((r : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * C =
        C * (((r : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) :
    Nat.card R ≤ 9 := by
  classical
  haveI : FiniteDimensional K (Fin 6 → K) := FiniteDimensional.finiteDimensional_pi K
  have hlamval3 : (lam : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hlam3]; rfl
  have hlamsum : (lam : K) ^ 2 + (lam : K) + 1 = 0 :=
    cube_sum_of_unit_ne_one hlam3 hlamne
  have hlam_inv : lam⁻¹ = lam ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    calc lam * lam ^ 2 = lam ^ (1 + 2) := by simpa using (pow_add lam 1 2).symm
      _ = lam ^ 3 := by norm_num
      _ = 1 := hlam3
  have hlam_inv_val : (lam : K)⁻¹ = (lam : K) ^ 2 := by
    rw [← Units.val_inv_eq_inv_val, hlam_inv]; rfl
  let f : Module.End K (Fin 6 → K) := Matrix.toLin' M
  let e : Fin 3 → K := ![1, (lam : K), (lam : K) ^ 2]
  have he2 : e 2 = (lam : K) ^ 2 := by simp [e]
  let V0 : Submodule K (Fin 6 → K) := f.eigenspace 1
  let V1 : Submodule K (Fin 6 → K) := f.eigenspace (lam : K)
  let V2 : Submodule K (Fin 6 → K) := f.eigenspace ((lam : K) ^ 2)
  let gC : (Fin 6 → K) ≃ₗ[K] (Fin 6 → K) :=
    { toFun := Matrix.toLin' C
      map_add' := fun x y => map_add (Matrix.toLin' C) x y
      map_smul' := fun a x => map_smul (Matrix.toLin' C) a x
      invFun := Matrix.toLin' C⁻¹
      left_inv := by
        intro v
        rw [← Matrix.toLin'_mul_apply, Matrix.nonsing_inv_mul C hCdet, Matrix.toLin'_one]
        rfl
      right_inv := by
        intro v
        rw [← Matrix.toLin'_mul_apply, Matrix.mul_nonsing_inv C hCdet, Matrix.toLin'_one]
        rfl }
  have htoLin_scalar : ∀ a : K,
      Matrix.toLin' (Matrix.scalar (Fin 6) a) = a • (1 : Module.End K (Fin 6 → K)) := by
    intro a
    apply LinearMap.ext
    intro v
    ext i
    simp [Matrix.toLin'_apply', Matrix.mulVec, Matrix.scalar_apply, Finset.sum_ite_eq']
  have hmap_mul : ∀ (mu : K) (w : Fin 6 → K), f w = mu • w →
      f (gC w) = ((lam : K)⁻¹ * mu) • gC w := by
    intro mu w hw
    change (Matrix.toLin' M) (Matrix.toLin' C w) =
      ((lam : K)⁻¹ * mu) • Matrix.toLin' C w
    rw [← Matrix.toLin'_mul_apply, hrel]
    rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply]
    rw [htoLin_scalar]
    simp only [LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply]
    rw [hw]
    rw [map_smul, smul_smul, Units.val_inv_eq_inv_val]
  have hmap2 : Submodule.map gC.toLinearMap V2 ≤ V1 := by
    rintro w ⟨v, hv, rfl⟩
    change v ∈ f.eigenspace (e 2) at hv
    change gC v ∈ f.eigenspace (e 1)
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : f v = (lam : K) ^ 2 • v := by simpa [e, he2] using hv
    have h := hmap_mul ((lam : K) ^ 2) v (by simpa using hv')
    have hcoef : (lam : K)⁻¹ * (lam : K) ^ 2 = (lam : K) := by
      rw [hlam_inv_val]
      calc (lam : K) ^ 2 * (lam : K) ^ 2 = (lam : K) ^ 4 := by ring
        _ = (lam : K) ^ 3 * (lam : K) := by ring
        _ = 1 * (lam : K) := by rw [hlamval3]
        _ = (lam : K) := one_mul _
    simpa [e, hcoef] using h
  have hmap1 : Submodule.map gC.toLinearMap V1 ≤ V0 := by
    rintro w ⟨v, hv, rfl⟩
    change v ∈ f.eigenspace (e 1) at hv
    change gC v ∈ f.eigenspace (e 0)
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : f v = (lam : K) • v := by simpa [e] using hv
    have h := hmap_mul ((lam : K)) v (by simpa using hv')
    have hcoef : (lam : K)⁻¹ * (lam : K) = 1 := by
      rw [hlam_inv_val]
      calc (lam : K) ^ 2 * (lam : K) = (lam : K) ^ 3 := by ring
        _ = 1 := hlamval3
    simpa [e, hcoef] using h
  have hmap0 : Submodule.map gC.toLinearMap V0 ≤ V2 := by
    rintro w ⟨v, hv, rfl⟩
    change v ∈ f.eigenspace (e 0) at hv
    change gC v ∈ f.eigenspace (e 2)
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hv' : f v = (1 : K) • v := by simpa [e] using hv
    have h := hmap_mul (1 : K) v (by simpa using hv')
    simpa [e, hlam_inv_val] using h
  have mapsTo0 : ∀ (g : GL (Fin 6) K),
      (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * M =
        M * (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) →
      ∀ c : V0,
        Matrix.toLin' (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) (c : Fin 6 → K) ∈ V0 := by
    intro g hg c
    have hc : f (c : Fin 6 → K) = 1 • (c : Fin 6 → K) := by
      simpa using (Module.End.mem_eigenspace_iff).mp c.2
    rw [Module.End.mem_eigenspace_iff]
    change (Matrix.toLin' M) (Matrix.toLin' (((g : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K)) (c : Fin 6 → K)) = 1 • (Matrix.toLin' (((g : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K)) (c : Fin 6 → K))
    rw [← Matrix.toLin'_mul_apply, hg.symm, Matrix.toLin'_mul_apply, hc]
    simp
  let restrMap (g : GL (Fin 6) K)
      (hg : (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * M =
        M * (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) : V0 →ₗ[K] V0 :=
    ((Matrix.toLin' (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))).domRestrict V0).codRestrict
      V0
      (mapsTo0 g hg)
  have restrMap_coe (g : GL (Fin 6) K)
      (hg : (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * M =
        M * (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) (v : V0) :
      ((restrMap g hg v : V0) : Fin 6 → K) =
        Matrix.toLin' (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) v := rfl
  let restrEquiv (r : R) : V0 ≃ₗ[K] V0 :=
    { toFun := fun v => restrMap (r : GL (Fin 6) K) (hcomm r r.2).1 v
      map_add' := fun x y => (restrMap (r : GL (Fin 6) K) (hcomm r r.2).1).map_add x y
      map_smul' := fun a x => (restrMap (r : GL (Fin 6) K) (hcomm r r.2).1).map_smul a x
      invFun := fun v => restrMap ((r⁻¹ : R) : GL (Fin 6) K) (hcomm (r⁻¹) (R.inv_mem r.2)).1 v
      left_inv := by
        intro v
        apply Subtype.ext
        simp only [restrMap_coe]
        change Matrix.toLin' ((((r⁻¹ : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
          ((Matrix.toLin' (((r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) (v : Fin 6 → K)) =
            (v : Fin 6 → K)
        rw [← Matrix.toLin'_mul_apply]
        have hmul : ((((r⁻¹ : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
            (((r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
          rw [Subgroup.coe_inv]
          simpa using congrArg (fun u : GL (Fin 6) K => ((u : Matrix (Fin 6) (Fin 6) K)))
            (inv_mul_cancel (((r : R) : GL (Fin 6) K)))
        rw [hmul, Matrix.toLin'_one]; rfl
      right_inv := by
        intro v
        apply Subtype.ext
        simp only [restrMap_coe]
        change Matrix.toLin' ((((r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
          ((Matrix.toLin' ((((r⁻¹ : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)))
            (v : Fin 6 → K)) = (v : Fin 6 → K)
        rw [← Matrix.toLin'_mul_apply]
        have hmul : ((((r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
            ((((r⁻¹ : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) = 1 := by
          rw [Subgroup.coe_inv]
          simpa using congrArg (fun u : GL (Fin 6) K => ((u : Matrix (Fin 6) (Fin 6) K)))
            (mul_inv_cancel (((r : R) : GL (Fin 6) K)))
        rw [hmul, Matrix.toLin'_one]; rfl }
  have restrEquiv_coe (r : R) (v : V0) :
      ((restrEquiv r v : V0) : Fin 6 → K) =
        Matrix.toLin' (((r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) (v : Fin 6 → K) := rfl
  let ρ : R →* LinearMap.GeneralLinearGroup K V0 :=
    { toFun := fun r => LinearMap.GeneralLinearGroup.ofLinearEquiv (restrEquiv r)
      map_one' := by
        apply Units.ext
        apply LinearMap.ext
        intro v
        change ((restrEquiv 1) v : V0) = v
        apply Subtype.ext
        simp only [restrEquiv, restrMap_coe]
        change Matrix.toLin' ((((1 : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
          (v : Fin 6 → K) = (v : Fin 6 → K)
        rw [show (((1 : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 by
          rw [Subgroup.coe_one]; rfl, Matrix.toLin'_one]
        rfl
      map_mul' := by
        intro r s
        apply Units.ext
        apply LinearMap.ext
        intro v
        change ((restrEquiv (r * s)) v : V0) = (restrEquiv r) ((restrEquiv s) v)
        apply Subtype.ext
        simp only [restrEquiv, restrMap_coe]
        change Matrix.toLin' ((((r * s : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
            (v : Fin 6 → K) =
          Matrix.toLin' (((r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
            (Matrix.toLin' (((s : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) (v : Fin 6 → K))
        rw [Subgroup.coe_mul, ← Matrix.toLin'_mul_apply]
        rfl }
  have hρinj : Function.Injective ρ := by
    intro r s hrs
    have hsuff : ρ (s⁻¹ * r) = 1 := by
      rw [map_mul, map_inv, hrs]
      group
    have hUM : ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * M =
        M * ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
      (hcomm (s⁻¹ * r) (R.mul_mem (R.inv_mem s.2) r.2)).1
    have hUC : ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) * C =
        C * ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :=
      (hcomm (s⁻¹ * r) (R.mul_mem (R.inv_mem s.2) r.2)).2
    have hfix0 : ∀ v ∈ V0, Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K)) v = v := by
      intro v hv
      have h1 : (LinearMap.GeneralLinearGroup.generalLinearEquiv K V0) (ρ (s⁻¹ * r)) =
          (1 : V0 ≃ₗ[K] V0) := by rw [hsuff]; rfl
      have h2 : (restrEquiv (s⁻¹ * r)) ⟨v, hv⟩ = ⟨v, hv⟩ := by
        have := congrArg (fun e : V0 ≃ₗ[K] V0 => e ⟨v, hv⟩) h1
        simpa [ρ, LinearMap.GeneralLinearGroup.generalLinearEquiv, restrEquiv] using this
      have h3 := congrArg Subtype.val h2
      rw [restrEquiv_coe] at h3
      exact h3
    have hCU : ∀ w : Fin 6 → K,
        Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
          (Matrix.toLin' C w) =
        Matrix.toLin' C (Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) w) := by
      intro w
      calc
        Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
            (Matrix.toLin' C w)
            = Matrix.toLin' (((((s⁻¹ * r : R) : GL (Fin 6) K) :
              Matrix (Fin 6) (Fin 6) K)) * C) w := by
              rw [← Matrix.toLin'_mul_apply]
        _ = Matrix.toLin' ((C * ((((s⁻¹ * r : R) : GL (Fin 6) K) :
              Matrix (Fin 6) (Fin 6) K)))) w := by
              rw [hUC]
        _ = Matrix.toLin' C (Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
              Matrix (Fin 6) (Fin 6) K)) w) := by
              rw [Matrix.toLin'_mul_apply]
    have hfix_all : ∀ v : Fin 6 → K,
        Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) v = v := by
      intro v
      obtain ⟨v0, hv0, v1, hv1, v2, hv2, hvsum⟩ :=
        cube_eigen_decomposition hK hM3 hlam3 hlamne v
      have h0 : Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) v0 = v0 := hfix0 v0 hv0
      have hc1 : Matrix.toLin' C v1 ∈ V0 := by
        have := hmap1 (Submodule.mem_map_of_mem hv1)
        simpa [gC] using this
      have h1 : Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) (Matrix.toLin' C v1) = Matrix.toLin' C v1 :=
        hfix0 _ hc1
      have hcommC1 := hCU v1
      have hu1 : Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) v1 = v1 := by
        apply gC.injective
        change Matrix.toLin' C (Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) v1) = Matrix.toLin' C v1
        rw [← hcommC1, h1]
      have hc2 : Matrix.toLin' C (Matrix.toLin' C v2) ∈ V0 := by
        have hcv2 : Matrix.toLin' C v2 ∈ V1 := by
          have := hmap2 (Submodule.mem_map_of_mem hv2)
          simpa [gC] using this
        have := hmap1 (Submodule.mem_map_of_mem hcv2)
        simpa [gC] using this
      have h2 : Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) (Matrix.toLin' C (Matrix.toLin' C v2)) =
          Matrix.toLin' C (Matrix.toLin' C v2) := hfix0 _ hc2
      have hcommC2 : Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) (Matrix.toLin' C (Matrix.toLin' C v2)) =
          Matrix.toLin' C (Matrix.toLin' C (Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
            Matrix (Fin 6) (Fin 6) K)) v2)) := by
        calc
          Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
              (Matrix.toLin' C (Matrix.toLin' C v2))
              = Matrix.toLin' C (Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
                  Matrix (Fin 6) (Fin 6) K)) (Matrix.toLin' C v2)) := hCU (Matrix.toLin' C v2)
          _ = Matrix.toLin' C (Matrix.toLin' C (Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
                  Matrix (Fin 6) (Fin 6) K)) v2)) := by rw [hCU v2]
      have hu2 : Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) v2 = v2 := by
        apply (gC.trans gC).injective
        change Matrix.toLin' C (Matrix.toLin' C (Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) v2)) = Matrix.toLin' C (Matrix.toLin' C v2)
        rw [← hcommC2, h2]
      calc
        Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) v
            = Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
                (v0 + v1 + v2) := by rw [hvsum]
        _ = Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) v0 +
              Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) v1 +
              Matrix.toLin' ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) v2 := by
            rw [map_add, map_add]
        _ = v0 + v1 + v2 := by rw [h0, hu1, hu2]
        _ = v := hvsum.symm
    have hU1 : (((s⁻¹ * r : R) : GL (Fin 6) K)) = 1 := by
      apply Units.ext
      have hmat : ((((s⁻¹ * r : R) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) = 1 := by
        have h := hfix_all
        ext i j
        have hv := h (Pi.single j 1)
        have hcoord := congrFun hv i
        simpa [dotProduct, Matrix.toLin'_apply', Matrix.mulVec, Pi.single_apply, Matrix.mul_apply,
          Matrix.one_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hcoord
      simpa using hmat
    have hmul : s⁻¹ * r = 1 := by
      apply Subtype.ext
      exact hU1
    calc r = s * (s⁻¹ * r) := by group
      _ = s * 1 := by rw [hmul]
      _ = s := mul_one s
  have hdim0 : Module.finrank K V0 = 2 := by
    simpa [V0, f] using dim_eigenspace_one_eq_two hK hM3 hlam3 hlamne hrel hCdet
  haveI : Fintype K := Fintype.ofFinite K
  have hGLcard : Nat.card (LinearMap.GeneralLinearGroup K V0) = 180 := by
    let b : Module.Basis (Fin 2) K V0 := Module.finBasisOfFinrankEq K V0 hdim0
    let eGL : LinearMap.GeneralLinearGroup K V0 ≃* GL (Fin 2) K :=
      (LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
        (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := K)).symm
    calc Nat.card (LinearMap.GeneralLinearGroup K V0) = Nat.card (GL (Fin 2) K) :=
          Nat.card_congr eGL.toEquiv
      _ = 180 := by
          rw [Matrix.card_GL_field]
          have hq : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
          simp [hq]
  have hcardR : Nat.card R = Nat.card ρ.range := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤) hρinj,
      Subgroup.card_top]
  have hdvd : Nat.card R ∣ 180 := by
    rw [hcardR, ← hGLcard]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have hRcard : Nat.card R ≤ 9 := by
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    have hk2 : k ≤ 2 := by
      by_contra h
      have hpow : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      have h27 : 27 ∣ Nat.card R := by
        rw [hk]
        exact hpow
      have h27' : 27 ∣ 180 := h27.trans hdvd
      norm_num at h27'
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  exact hRcard

end Card

end CFSG.StandardType.USixTwo

end
