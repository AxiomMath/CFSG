module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiSinger

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {p f : ℕ} {ℓ : K}

theorem three_mul_succ_dvd {q : ℕ} (hq : q % 3 = 2) : 3 * (q + 1) ∣ q ^ 3 + 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
  exact ⟨3 * t ^ 2 + 3 * t + 1, by ring⟩

theorem root_pow_three (ℓ : K) :
    (AdjoinRoot.root (X ^ 3 - C ℓ : K[X])) ^ 3 = algebraMap K (cubeField ℓ) ℓ := by
  have h := AdjoinRoot.eval₂_root (X ^ 3 - C ℓ : K[X])
  rw [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem cubeField_eq (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) {y : Matrix (Fin 3) (Fin 3) K}
    (hy : y ^ 3 = ℓ • 1) (e : cubeField ℓ) : ∃ a b c : K,
      e = algebraMap K _ a + algebraMap K _ b * AdjoinRoot.root _ +
        algebraMap K _ c * AdjoinRoot.root _ ^ 2 := by
  obtain ⟨a, b, c, habc⟩ := (commute_iff_eq_poly hℓ hy (cubeHom hy e)).mp
    ((mem_range_cubeHom hℓ hy _).mp ⟨e, rfl⟩)
  refine ⟨a, b, c, cubeHom_injective hℓ hy ?_⟩
  rw [habc, map_add, map_add, map_mul, map_mul, map_pow, cubeHom_root, AlgHom.commutes,
    AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_mul_assoc, one_mul]

theorem card_cubeField_false (hK : PiField false p f K) (ℓ : K) :
    Nat.card (cubeField ℓ) = (p ^ f) ^ 6 := by
  have := hK.finite
  rw [card_cubeField, hK.card, piCard, Bool.cond_false, ← pow_mul]

theorem unitaryFieldData_cubeField (hK : PiField false p f K) (ℓ : K)
    [Fact (Irreducible (X ^ 3 - C ℓ : K[X]))] : UnitaryFieldData p (3 * f) (cubeField ℓ) where
  prime := hK.prime
  one_le := by have := hK.one_le; omega
  card := by rw [card_cubeField_false hK, ← pow_mul]; ring_nf

theorem bar_cubeField_apply [Fact (Irreducible (X ^ 3 - C ℓ : K[X]))]
    (h3 : UnitaryFieldData p (3 * f) (cubeField ℓ)) (e : cubeField ℓ) :
    h3.bar e = e ^ (p ^ f) ^ 3 := by
  rw [UnitaryFieldData.bar_apply, ← pow_mul, mul_comm]

theorem pow_succ_eq_one_of_pow_three_eq (hK : PiField false p f K) {y : GL (Fin 3) K}
    (hyH : y ∈ glPi false 3 (p ^ f) K) (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) : ℓ ^ (p ^ f + 1) = 1 := by
  have hℓ0 : ℓ ≠ 0 := fun h0 => hℓ 0 (by rw [h0]; ring)
  have hy3 : y ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ℓ hℓ0) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hy, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Units.val_mk0]
  have hmem := pow_mem hyH 3
  rw [hy3, scalar_mem_glPi_false_iff hK.unitary] at hmem
  simpa using hmem

theorem cubeHom_bar (hK : PiField false p f K) (hq : ModThree false (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi false 3 (p ^ f) K) (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) [Fact (Irreducible (X ^ 3 - C ℓ : K[X]))]
    (h3 : UnitaryFieldData p (3 * f) (cubeField ℓ)) (e : cubeField ℓ) :
    cubeHom hy (h3.bar e) = ((cubeHom hy e).map hK.unitary.bar)ᵀ := by
  have h := hK.unitary
  have := hK.finite
  have := Fintype.ofFinite K
  have hq2 : p ^ f % 3 = 2 := hq
  have hKcard : Nat.card K = (p ^ f) ^ 2 := by rw [hK.card, piCard, Bool.cond_false]
  have hℓn := pow_succ_eq_one_of_pow_three_eq hK hyH hℓ hy
  set α := AdjoinRoot.root (X ^ 3 - C ℓ : K[X])
  have hα : α ^ ((p ^ f) ^ 3 + 1) = 1 := by
    obtain ⟨k, hk⟩ := three_mul_succ_dvd hq2
    rw [hk, pow_mul, pow_mul, root_pow_three, ← map_pow, hℓn, map_one, one_pow]
  have hα0 : α ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by positivity)] at hα
    exact zero_ne_one hα
  have hφα : h3.bar α = α⁻¹ := by
    rw [bar_cubeField_apply]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hα])
  have hφK : ∀ a : K, h3.bar (algebraMap K _ a) = algebraMap K _ (h.bar a) := by
    intro a
    rw [bar_cubeField_apply, ← map_pow, h.bar_apply]
    congr 1
    calc a ^ (p ^ f) ^ 3 = (a ^ (p ^ f) ^ 2) ^ p ^ f := by ring
      _ = a ^ p ^ f := by rw [← hKcard, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hyinv : ((y : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ =
      ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have hu := (mem_glPi_false h).mp hyH
    calc ((y : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ =
        ((y : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (y * (y⁻¹ : GL (Fin 3) K)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = (y⁻¹ : GL (Fin 3) K) := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hψinv : cubeHom hy α⁻¹ = ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : cubeHom hy α⁻¹ * y = 1 := by
      calc cubeHom hy α⁻¹ * y = cubeHom hy α⁻¹ * cubeHom hy α := by rw [cubeHom_root]
        _ = cubeHom hy (α⁻¹ * α) := (map_mul _ _ _).symm
        _ = 1 := by rw [inv_mul_cancel₀ hα0, map_one]
    calc cubeHom hy α⁻¹ = cubeHom hy α⁻¹ * (y * (y⁻¹ : GL (Fin 3) K)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = (y⁻¹ : GL (Fin 3) K) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨a, b, c, rfl⟩ := cubeField_eq hℓ hy e
  set yi := ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hL : cubeHom hy (h3.bar (algebraMap K _ a + algebraMap K _ b * α +
      algebraMap K _ c * α ^ 2)) = h.bar a • 1 + h.bar b • yi + h.bar c • yi ^ 2 := by
    simp only [map_add, map_mul, map_pow, hφK, hφα]
    simp only [AlgHom.commutes, hψinv]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hR : cubeHom hy (algebraMap K _ a + algebraMap K _ b * α + algebraMap K _ c * α ^ 2) =
      a • 1 + b • (y : Matrix (Fin 3) (Fin 3) K) + c • (y : Matrix (Fin 3) (Fin 3) K) ^ 2 := by
    have hroot : cubeHom hy α = y := cubeHom_root hy
    simp only [map_add, map_mul, map_pow, AlgHom.commutes, hroot]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rw [hL, hR]
  have hmapsq : (((y : Matrix (Fin 3) (Fin 3) K) ^ 2).map h.bar)ᵀ = yi ^ 2 := by
    rw [sq, Matrix.map_mul, Matrix.transpose_mul, hyinv, sq]
  rw [Matrix.map_add _ (map_add h.bar), Matrix.map_add _ (map_add h.bar), Matrix.transpose_add,
    Matrix.transpose_add]
  rw [Matrix.map_smul' _ _ _ (fun x y => map_mul h.bar x y),
    Matrix.map_smul' _ _ _ (fun x y => map_mul h.bar x y),
    Matrix.map_smul' _ _ _ (fun x y => map_mul h.bar x y),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_one, hyinv, hmapsq]

theorem card_centralizer_glPi_false (hK : PiField false p f K) (hq : ModThree false (p ^ f))
    {y : GL (Fin 3) K} (hyH : y ∈ glPi false 3 (p ^ f) K) (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    Nat.card ↥(glPi false 3 (p ^ f) K ⊓ Subgroup.centralizer {y}) = (p ^ f) ^ 3 + 1 := by
  have h := hK.unitary
  have : Fact (Irreducible (X ^ 3 - C ℓ : K[X])) := ⟨irreducible_X_pow_three_sub_C hℓ⟩
  have h3 := unitaryFieldData_cubeField hK ℓ
  have hEcard := card_cubeField_false hK ℓ
  have : Finite (cubeField ℓ) := Nat.finite_of_card_ne_zero (by
    rw [hEcard]; exact pow_ne_zero _ (pow_ne_zero _ hK.prime.ne_zero))
  have key := cubeHom_bar hK hq hyH hℓ hy h3
  have hset : glPi false 3 (p ^ f) K ⊓ Subgroup.centralizer {y} =
      (rootsOfUnity ((p ^ f) ^ 3 + 1) (cubeField ℓ)).map (cubeUnitsHom hy) := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgH, hgC⟩ := Subgroup.mem_inf.mp hg
      rw [← range_cubeUnitsHom hℓ hy] at hgC
      obtain ⟨e, rfl⟩ := hgC
      refine ⟨e, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_rootsOfUnity]
      have hu := (mem_glPi_false h).mp hgH
      rw [coe_cubeUnitsHom, ← key, ← map_mul] at hu
      have he : h3.bar (e : cubeField ℓ) * e = 1 :=
        cubeHom_injective hℓ hy (by rw [hu, map_one])
      rw [bar_cubeField_apply, ← pow_succ] at he
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact he)
    · rintro ⟨e, he, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_glPi_false h, coe_cubeUnitsHom, ← key, ← map_mul, bar_cubeField_apply,
          ← pow_succ]
        have := congrArg Units.val ((mem_rootsOfUnity _ _).mp he)
        rw [Units.val_pow_eq_pow_val, Units.val_one] at this
        rw [this, map_one]
      · rw [← range_cubeUnitsHom hℓ hy]
        exact ⟨e, rfl⟩
  rw [hset, Subgroup.card_map_of_injective (cubeUnitsHom_injective hℓ hy)]
  have : NeZero ((p ^ f) ^ 3 + 1) := ⟨Nat.succ_ne_zero _⟩
  refine CFSG.LinearGroups.card_rootsOfUnity_of_dvd ?_
  rw [hEcard]
  have h1 : 1 ≤ (p ^ f) ^ 3 := Nat.one_le_pow _ _ (pow_pos hK.prime.pos f)
  refine ⟨(p ^ f) ^ 3 - 1, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, (p ^ f) ^ 3 = k + 1 := ⟨(p ^ f) ^ 3 - 1, by omega⟩
  rw [show (p ^ f) ^ 6 = ((p ^ f) ^ 3) ^ 2 by ring, hk, Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

theorem exists_w_unitary (hK : PiField false p f K) (hq : ModThree false (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {y : GL (Fin 3) K} (hyH : y ∈ glPi false 3 (p ^ f) K) (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    ∃ w ∈ slPi false 3 (p ^ f) K,
      (w : Matrix (Fin 3) (Fin 3) K) * y = τ • ((y : Matrix (Fin 3) (Fin 3) K) * w) := by
  have h := hK.unitary
  have : Fact (Irreducible (X ^ 3 - C ℓ : K[X])) := ⟨irreducible_X_pow_three_sub_C hℓ⟩
  have h3 := unitaryFieldData_cubeField hK ℓ
  have key := cubeHom_bar hK hq hyH hℓ hy h3
  have ct_mul : ∀ A B : Matrix (Fin 3) (Fin 3) K,
      ((A * B).map h.bar)ᵀ = (B.map h.bar)ᵀ * (A.map h.bar)ᵀ := fun A B => by
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have ct_smul : ∀ (c : K) (A : Matrix (Fin 3) (Fin 3) K),
      ((c • A).map h.bar)ᵀ = h.bar c • (A.map h.bar)ᵀ := fun c A => by
    rw [Matrix.map_smul' _ _ _ (fun x y => map_mul h.bar x y), Matrix.transpose_smul]
  have ct_ct : ∀ A : Matrix (Fin 3) (Fin 3) K, (((A.map h.bar)ᵀ).map h.bar)ᵀ = A := fun A => by
    ext i j
    simp [h.bar_bar]
  set Y := (y : Matrix (Fin 3) (Fin 3) K) with hYdef
  have hYu : (Y.map h.bar)ᵀ * Y = 1 := (mem_glPi_false h).mp hyH
  have hYu' : Y * (Y.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hYu
  have hτb : τ * h.bar τ = 1 := by
    rw [h.bar_apply, ← pow_succ']
    exact pow_succ_eq_one_of_modThree hq hτ
  obtain ⟨w₀, hw₀det, -, hw₀y⟩ := exists_w_linear hτ hτ1 hℓ hy
  set W := (w₀ : Matrix (Fin 3) (Fin 3) K) with hWdef
  set Wc := (W.map h.bar)ᵀ with hWc
  have h1 : (Y.map h.bar)ᵀ * Wc = h.bar τ • (Wc * (Y.map h.bar)ᵀ) := by
    rw [hWc, ← ct_mul, hw₀y, ct_smul, ct_mul]
  have h2 : Wc * Y = h.bar τ • (Y * Wc) := by
    calc Wc * Y = Y * ((Y.map h.bar)ᵀ * Wc) * Y := by
          rw [← Matrix.mul_assoc, hYu', Matrix.one_mul]
      _ = h.bar τ • (Y * Wc * ((Y.map h.bar)ᵀ * Y)) := by
          rw [h1, Matrix.mul_smul, Matrix.smul_mul]
          simp only [Matrix.mul_assoc]
      _ = h.bar τ • (Y * Wc) := by rw [hYu, Matrix.mul_one]
  set M := Wc * W with hMdef
  have hMy : M * Y = Y * M := by
    calc M * Y = Wc * (W * Y) := Matrix.mul_assoc _ _ _
      _ = τ • (Wc * Y * W) := by rw [hw₀y, Matrix.mul_smul, Matrix.mul_assoc]
      _ = (τ * h.bar τ) • (Y * M) := by
          rw [h2, Matrix.smul_mul, smul_smul, hMdef, Matrix.mul_assoc]
      _ = Y * M := by rw [hτb, one_smul]
  have hMh : (M.map h.bar)ᵀ = M := by rw [hMdef, ct_mul, hWc, ct_ct]
  obtain ⟨m, hm⟩ := (mem_range_cubeHom hℓ hy M).mpr hMy
  have hmfix : h3.bar m = m := by
    apply cubeHom_injective hℓ hy
    rw [key, hm, hMh]
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero] at hm
    have := congrArg Matrix.det hm
    rw [det_zero, hMdef, det_mul, hWc, det_transpose,
      show (W.map h.bar).det = h.bar W.det from (RingHom.map_det h.bar _).symm, hw₀det, map_one,
      one_mul] at this
    exact zero_ne_one this
  obtain ⟨δ, hδ⟩ := h3.normHom_surjective ⟨m⁻¹, h3.mem_fixedField.mpr (by rw [map_inv₀, hmfix])⟩
  have hδm : δ * h3.bar δ * m = 1 := by
    have := congrArg Subtype.val hδ
    simp only [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at this
    rw [this, inv_mul_cancel₀ hm0]
  set D := cubeHom hy δ with hDdef
  set W₁ := W * D with hW₁
  have hW₁u : (W₁.map h.bar)ᵀ * W₁ = 1 := by
    rw [hW₁, ct_mul, hDdef, ← key]
    calc cubeHom hy (h3.bar δ) * Wc * (W * cubeHom hy δ) =
        cubeHom hy (h3.bar δ) * M * cubeHom hy δ := by
          simp only [hMdef, Matrix.mul_assoc]
      _ = cubeHom hy (h3.bar δ * m * δ) := by rw [map_mul, map_mul, hm]
      _ = 1 := by rw [show h3.bar δ * m * δ = δ * h3.bar δ * m by ring, hδm, map_one]
  have hW₁y : W₁ * Y = τ • (Y * W₁) := by
    have hDY : D * Y = Y * D := (mem_range_cubeHom hℓ hy D).mp ⟨δ, rfl⟩
    calc W₁ * Y = W * (D * Y) := Matrix.mul_assoc _ _ _
      _ = W * Y * D := by rw [hDY, Matrix.mul_assoc]
      _ = τ • (Y * W₁) := by rw [hw₀y, Matrix.smul_mul, hW₁, Matrix.mul_assoc]
  have hW₁unit : IsUnit W₁ :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hW₁u)
  set w₁ := hW₁unit.unit with hw₁
  have hw₁m : (w₁ : Matrix (Fin 3) (Fin 3) K) = W₁ := IsUnit.unit_spec hW₁unit
  have hw₁H : w₁ ∈ glPi false 3 (p ^ f) K := by
    rw [mem_glPi_false h, hw₁m]
    exact hW₁u
  obtain ⟨d, hd⟩ : (⟨GeneralLinearGroup.det w₁, det_mem_rootsOfUnity hK hw₁H⟩ :
      rootsOfUnity (qSubPi false (p ^ f)) K)⁻¹ ∈ (detCent hK y).range := by
    rw [range_detCent hK hq hyH hℓ hy]
    exact Subgroup.mem_top _
  obtain ⟨hdH, hdC⟩ := Subgroup.mem_inf.mp d.2
  have hdy : (d : GL (Fin 3) K) * y = y * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
  have hddet : (GeneralLinearGroup.det (d : GL (Fin 3) K) : K) *
      (GeneralLinearGroup.det w₁ : K) = 1 := by
    have := congrArg (fun t : rootsOfUnity _ K => ((t : Kˣ) : K)) hd
    simp only [detCent, MonoidHom.coe_mk, OneHom.coe_mk] at this
    have hne : (w₁ : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp w₁.isUnit).ne_zero
    rw [this]
    simp only [InvMemClass.coe_inv, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply]
    exact inv_mul_cancel₀ hne
  refine ⟨w₁ * (d : GL (Fin 3) K), (mem_slPi_false h).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [Units.val_mul, det_mul, mul_comm]
    simpa using hddet
  · exact (mem_glPi_false h).mp (mul_mem hw₁H hdH)
  · have hdy' : ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Y =
        Y * ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg Units.val hdy
      simpa using this
    rw [Units.val_mul, hw₁m, Matrix.mul_assoc, hdy', ← Matrix.mul_assoc, hW₁y, Matrix.smul_mul,
      Matrix.mul_assoc]

end CFSG.RankThree.PartTwo.Sec4
