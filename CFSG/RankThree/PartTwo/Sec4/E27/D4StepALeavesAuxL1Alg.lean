module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open Matrix

section Rational

variable {k Ω : Type} [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]

theorem exists_rational_scalar_mul {q : ℕ} (hq : 2 ≤ q) (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ q)
    (hk : ∀ c : k, Fr (algebraMap k Ω c) = algebraMap k Ω c)
    (hfix : ∀ z : Ω, Fr z = z → ∃ c : k, algebraMap k Ω c = z)
    (N : GL (Fin 3) Ω)
    (hN : ∀ i j : Fin 3, i ≠ j → ∀ a b : Fin 3, ∃ c : k, algebraMap k Ω c =
      (((N : Matrix (Fin 3) (Fin 3) Ω) * (1 + Matrix.single i j (1 : Ω)) *
        ((N⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) a b)) :
    ∃ (M : GL (Fin 3) k) (c : Ω), c ≠ 0 ∧
      (N : Matrix (Fin 3) (Fin 3) Ω) =
        c • ((M : Matrix (Fin 3) (Fin 3) k).map (algebraMap k Ω)) := by
  classical
  set A : Matrix (Fin 3) (Fin 3) Ω := (N : Matrix (Fin 3) (Fin 3) Ω) with hA
  set A' : Matrix (Fin 3) (Fin 3) Ω := ((N⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) with hA'
  have hAA' : A * A' = 1 := by rw [hA, hA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA'A : A' * A = 1 := by rw [hA, hA', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set φ : Matrix (Fin 3) (Fin 3) Ω →+* Matrix (Fin 3) (Fin 3) Ω := Fr.mapMatrix with hφ
  have hφapp : ∀ B : Matrix (Fin 3) (Fin 3) Ω, φ B = B.map Fr := fun B => rfl
  set P : Matrix (Fin 3) (Fin 3) Ω := A' * φ A with hP
  have e2 : φ A' * φ A = 1 := by rw [← map_mul, hA'A, map_one]
  have hcomm : ∀ i j : Fin 3, i ≠ j → Commute (Matrix.single i j (1 : Ω)) P := by
    intro i j hij
    set T : Matrix (Fin 3) (Fin 3) Ω := 1 + Matrix.single i j 1 with hT
    have hφT : φ T = T := by
      rw [hT, map_add, map_one, hφapp]
      congr 1
      ext a b
      simp only [Matrix.map_apply, Matrix.single_apply]
      split_ifs <;> simp
    have hB : φ (A * T * A') = A * T * A' := by
      ext a b
      obtain ⟨c, hc⟩ := hN i j hij a b
      show Fr ((A * T * A') a b) = (A * T * A') a b
      rw [← hc]
      exact hk c
    have h1 : φ A * T * φ A' = A * T * A' := by
      calc φ A * T * φ A' = φ A * φ T * φ A' := by rw [hφT]
        _ = φ (A * T * A') := by rw [map_mul, map_mul]
        _ = A * T * A' := hB
    have e1 : T * A' = A' * (φ A * T * φ A') := by
      rw [h1]
      calc T * A' = (A' * A) * T * A' := by rw [hA'A, Matrix.one_mul]
        _ = A' * (A * T * A') := by simp only [Matrix.mul_assoc]
    have h2 : T * P = P * T := by
      calc T * P = T * A' * φ A := by rw [hP, Matrix.mul_assoc]
        _ = A' * (φ A * T * φ A') * φ A := by rw [e1]
        _ = A' * φ A * T * (φ A' * φ A) := by simp only [Matrix.mul_assoc]
        _ = P * T := by rw [e2, Matrix.mul_one]
    have h3 : (1 + Matrix.single i j (1 : Ω)) * P = P * (1 + Matrix.single i j (1 : Ω)) := h2
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at h3
    exact add_left_cancel h3
  obtain ⟨lam, hlam⟩ := Matrix.mem_range_scalar_of_commute_single (fun i j hij => hcomm i j hij)
  have hφA : φ A = lam • A := by
    have h1 : A * P = φ A := by
      rw [hP, ← Matrix.mul_assoc, hAA', Matrix.one_mul]
    rw [← h1, ← hlam, Matrix.scalar_apply]
    ext a b
    simp [Matrix.mul_diagonal, Matrix.smul_apply, mul_comm]
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hφA
    have : (1 : Matrix (Fin 3) (Fin 3) Ω) = 0 := by
      rw [← map_one φ, ← hAA', map_mul, hφA, zero_mul]
    exact one_ne_zero this
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq lam⁻¹ (n := q - 1) (by omega)
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hc
    exact inv_ne_zero hlam0 hc.symm
  have hcq : c ^ q * lam = c := by
    have : q = (q - 1) + 1 := by omega
    calc c ^ q * lam = c * (c ^ (q - 1) * lam) := by
          conv_lhs => rw [this, pow_succ]
          ring
      _ = c := by rw [hc, inv_mul_cancel₀ hlam0, mul_one]
  have hM₀ : ∀ a b : Fin 3, Fr ((c • A) a b) = (c • A) a b := by
    intro a b
    have h1 := congrFun (congrFun hφA a) b
    rw [hφapp, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, h1, hFr c]
    calc c ^ q * (lam * A a b) = (c ^ q * lam) * A a b := by ring
      _ = c * A a b := by rw [hcq]
  choose m hm using fun a b => hfix _ (hM₀ a b)
  set M₁ : Matrix (Fin 3) (Fin 3) k := Matrix.of fun a b => m a b with hM₁
  have hM₁map : M₁.map (algebraMap k Ω) = c • A := by
    ext a b
    exact hm a b
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 ⟨N, rfl⟩
  have hdet : M₁.det ≠ 0 := by
    intro h0
    have : (M₁.map (algebraMap k Ω)).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    rw [hM₁map, Matrix.det_smul] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hc0 (pow_eq_zero_iff (by norm_num) |>.1 h)
    · exact hdetA.ne_zero h
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M₁ hdet, c⁻¹, inv_ne_zero hc0, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hM₁map, smul_smul, inv_mul_cancel₀ hc0,
    one_smul]

end Rational

section LinearAssembly

variable {G₀ : Type*} [Group G₀]

@[expose] noncomputable def conjMapSL {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (H₀ : Matrix.SpecialLinearGroup (Fin 3) Ω) :
    Matrix.SpecialLinearGroup (Fin 3) k →* Matrix.SpecialLinearGroup (Fin 3) Ω :=
  (MulAut.conj H₀).toMonoidHom.comp (Matrix.SpecialLinearGroup.map (algebraMap k Ω))

theorem conjMapSL_apply {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (H₀ : Matrix.SpecialLinearGroup (Fin 3) Ω) (Y : Matrix.SpecialLinearGroup (Fin 3) k) :
    conjMapSL H₀ Y = H₀ * Matrix.SpecialLinearGroup.map (algebraMap k Ω) Y * H₀⁻¹ := rfl

theorem conjMapSL_injective {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (H₀ : Matrix.SpecialLinearGroup (Fin 3) Ω) : Function.Injective (conjMapSL (k := k) H₀) := by
  refine (MulAut.conj H₀).injective.comp ?_
  intro A B h
  exact Subtype.ext (Matrix.map_injective (algebraMap k Ω).injective (congrArg Subtype.val h))

theorem coe_conj_eq_of_eq_smul {R : Type*} [Field R] (N : GL (Fin 3) R)
    (B B' : Matrix (Fin 3) (Fin 3) R) (c : R) (hc : c ≠ 0)
    (hN : (N : Matrix (Fin 3) (Fin 3) R) = c • B) (hBB' : B * B' = 1)
    (Z : Matrix (Fin 3) (Fin 3) R) :
    (N : Matrix (Fin 3) (Fin 3) R) * Z * ((N⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      B * Z * B' := by
  have hB : B = c⁻¹ • (N : Matrix (Fin 3) (Fin 3) R) := by
    rw [hN, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hNN' : ((N⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (N : Matrix (Fin 3) (Fin 3) R)
      = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv : ((N⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = c⁻¹ • B' := by
    calc ((N⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
        = ((N⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (B * B') := by
          rw [hBB', Matrix.mul_one]
      _ = ((N⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
            ((c⁻¹ • (N : Matrix (Fin 3) (Fin 3) R)) * B') := by rw [← hB]
      _ = c⁻¹ • B' := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hNN', Matrix.one_mul]
  rw [hinv, hN]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, inv_mul_cancel₀ hc,
    one_smul]

theorem linear_layer_model_of_interface (D C : Subgroup G₀)
    (hnorm : ∀ g ∈ C, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    {k Ω : Type} [Field k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    {q : ℕ} (hq : 2 ≤ q) (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ q)
    (hk : ∀ c : k, Fr (algebraMap k Ω c) = algebraMap k Ω c)
    (hfix : ∀ z : Ω, Fr z = z → ∃ c : k, algebraMap k Ω c = z)
    (s : D →* Matrix.SpecialLinearGroup (Fin 3) Ω) (hs : Function.Injective s)
    (H₀ : Matrix.SpecialLinearGroup (Fin 3) Ω)
    (hrange : ∀ X : Matrix.SpecialLinearGroup (Fin 3) Ω,
      X ∈ s.range ↔ X ∈ (conjMapSL (k := k) H₀).range)
    (hact : ∀ g ∈ C, ∃ N : GL (Fin 3) Ω, ∀ d d' : D, (d' : G₀) = g * d * g⁻¹ →
      Matrix.SpecialLinearGroup.toGL (s d') =
        N * Matrix.SpecialLinearGroup.toGL (s d) * N⁻¹) :
    ∃ e : D ≃* Matrix.SpecialLinearGroup (Fin 3) k, ∀ g ∈ C, ∃ M : GL (Fin 3) k,
      ∀ d d' : D, (d' : G₀) = g * d * g⁻¹ →
        ((e d' : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
          (M : Matrix (Fin 3) (Fin 3) k) *
            ((e d : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
              ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
  classical
  have he₀inj := conjMapSL_injective (k := k) (Ω := Ω) H₀
  have hrange_eq : s.range = (conjMapSL (k := k) H₀).range := Subgroup.ext hrange
  let eD : D ≃* Matrix.SpecialLinearGroup (Fin 3) k :=
    ((MonoidHom.ofInjective hs).trans (MulEquiv.subgroupCongr hrange_eq)).trans
      (MonoidHom.ofInjective he₀inj).symm
  have heD : ∀ d : D, conjMapSL (k := k) H₀ (eD d) = s d := fun d =>
    MonoidHom.apply_ofInjective_symm he₀inj
      (MulEquiv.subgroupCongr hrange_eq (MonoidHom.ofInjective hs d))
  refine ⟨eD, fun g hg => ?_⟩
  obtain ⟨N, hN⟩ := hact g hg
  set H : GL (Fin 3) Ω := Matrix.SpecialLinearGroup.toGL H₀ with hH
  set N' : GL (Fin 3) Ω := H⁻¹ * N * H with hN'
  have key : ∀ d d' : D, (d' : G₀) = g * d * g⁻¹ →
      Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map (algebraMap k Ω) (eD d')) =
        N' * Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map (algebraMap k Ω) (eD d)) * N'⁻¹ := by
    intro d d' hdd'
    have h1 := hN d d' hdd'
    rw [← heD d', ← heD d, conjMapSL_apply, conjMapSL_apply] at h1
    simp only [map_mul, map_inv] at h1
    set T' := Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map (algebraMap k Ω) (eD d')) with hT'
    set T := Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map (algebraMap k Ω) (eD d)) with hT
    rw [← hH] at h1
    have e1 : T' = H⁻¹ * (H * T' * H⁻¹) * H := by group
    rw [e1, h1, hN']
    group
  have hrat : ∀ i j : Fin 3, i ≠ j → ∀ a b : Fin 3, ∃ c : k, algebraMap k Ω c =
      (((N' : Matrix (Fin 3) (Fin 3) Ω) * (1 + Matrix.single i j (1 : Ω)) *
        ((N'⁻¹ : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) a b) := by
    intro i j hij a b
    set Y : Matrix.SpecialLinearGroup (Fin 3) k := Matrix.SpecialLinearGroup.transvection hij 1
    set d : D := eD.symm Y with hd
    have hdY : eD d = Y := MulEquiv.apply_symm_apply eD Y
    have hd' : g * (d : G₀) * g⁻¹ ∈ D := hnorm g hg d d.2
    have h1 := key d ⟨_, hd'⟩ rfl
    rw [hdY] at h1
    have h2 := congrArg (fun X : GL (Fin 3) Ω => (X : Matrix (Fin 3) (Fin 3) Ω)) h1
    simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h2
    refine ⟨((eD ⟨_, hd'⟩ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) a b, ?_⟩
    have h3 : (Y : Matrix (Fin 3) (Fin 3) k).map (algebraMap k Ω) =
        1 + Matrix.single i j (1 : Ω) := by
      rw [Matrix.SpecialLinearGroup.transvection_coe]
      ext x y
      simp [Matrix.single_apply, Matrix.one_apply]
    rw [h3] at h2
    have h4 := congrFun (congrFun h2 a) b
    rw [← h4]
    rfl
  obtain ⟨M, c, hc0, hNc⟩ := exists_rational_scalar_mul hq Fr hFr hk hfix N' hrat
  refine ⟨M, fun d d' hdd' => ?_⟩
  have h1 := key d d' hdd'
  have h2 := congrArg (fun X : GL (Fin 3) Ω => (X : Matrix (Fin 3) (Fin 3) Ω)) h1
  simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h2
  have hBB' : ((M : Matrix (Fin 3) (Fin 3) k).map (algebraMap k Ω)) *
      (((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).map (algebraMap k Ω)) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [coe_conj_eq_of_eq_smul N' _ _ c hc0 hNc hBB'] at h2
  have h3 : ((eD d' : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).map
      (algebraMap k Ω) = ((M : Matrix (Fin 3) (Fin 3) k) *
        ((eD d : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
          ((M⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).map (algebraMap k Ω) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    exact h2
  exact Matrix.map_injective (algebraMap k Ω).injective h3

end LinearAssembly

end CFSG.RankThree.PartTwo.Sec4.E27
