module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResL3ThreeReg
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMain

public section

namespace CFSG.StandardType.L3Three

open Matrix CFSG.StandardType.TypeA.PGLTor

variable {K : Type*} [Field K]

theorem injective_of_diagonal_mul_eq {r : Fin 3 → K} (hr : ∀ i, r i ≠ 0)
    {M : Matrix (Fin 3) (Fin 3) K} (hM : M.det ≠ 0) {a : K} (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1)
    (h : diagonal r * M = a • (M * diagonal r)) : Function.Injective r := by
  have hshift : ∀ j, ∃ i, r i = a * r j := by
    intro j
    by_contra hcon
    push Not at hcon
    apply hM
    refine det_eq_zero_of_column_eq_zero j fun i => ?_
    have h1 := congrFun (congrFun h i) j
    rw [diagonal_mul, Matrix.smul_apply, mul_diagonal, smul_eq_mul] at h1
    have h2 : (r i - a * r j) * M i j = 0 := by rw [sub_mul, h1]; ring
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (hcon i))
  choose σ hσ using hshift
  have := Fact.mk Nat.prime_three
  have hprim : IsPrimitiveRoot a 3 := (orderOf_eq_prime ha3 ha1) ▸ IsPrimitiveRoot.orderOf a
  have hpinj : ∀ x y : Fin 3, a ^ (x : ℕ) * r 0 = a ^ (y : ℕ) * r 0 → x = y := fun x y h =>
    Fin.ext (hprim.pow_inj x.isLt y.isLt (mul_right_cancel₀ (hr 0) h))
  set g : Fin 3 → Fin 3 := ![0, σ 0, σ (σ 0)] with hg
  have hrg : ∀ k, r (g k) = a ^ (k : ℕ) * r 0 := by
    intro k
    fin_cases k
    · simp [hg]
    · simp [hg, hσ]
    · simp only [hg, Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      rw [hσ, hσ]
      ring
  have hginj : Function.Injective g := fun x y hxy => hpinj x y (by rw [← hrg, ← hrg, hxy])
  have hgsurj : Function.Surjective g := Finite.surjective_of_injective hginj
  intro x y hxy
  obtain ⟨x', rfl⟩ := hgsurj x
  obtain ⟨y', rfl⟩ := hgsurj y
  rw [hrg, hrg] at hxy
  rw [hpinj x' y' hxy]

theorem exists_simple_entry {α : Type*} {r : Fin 3 → α} (hinj : ¬ Function.Injective r)
    (hconst : ∃ i j, r i ≠ r j) : ∃ i₀, ∀ j, j ≠ i₀ → r j ≠ r i₀ := by
  by_cases h01 : r 0 = r 1
  · by_cases h02 : r 0 = r 2
    · exfalso
      obtain ⟨i, j, hij⟩ := hconst
      apply hij
      fin_cases i <;> fin_cases j <;> simp_all
    · refine ⟨2, fun j hj => ?_⟩
      fin_cases j
      · exact h02
      · show r 1 ≠ r 2
        rw [← h01]
        exact h02
      · exact absurd rfl hj
  · by_cases h02 : r 0 = r 2
    · refine ⟨1, fun j hj => ?_⟩
      fin_cases j
      · exact h01
      · exact absurd rfl hj
      · show r 2 ≠ r 1
        rw [← h02]
        exact h01
    · by_cases h12 : r 1 = r 2
      · refine ⟨0, fun j hj => ?_⟩
        fin_cases j
        · exact absurd rfl hj
        · exact fun h => h01 h.symm
        · show r 2 ≠ r 0
          rw [← h12]
          exact fun h => h01 h.symm
      · exfalso
        apply hinj
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem entry_eq_zero_of_simple {r : Fin 3 → K} {i₀ : Fin 3} (hi₀ : ∀ j, j ≠ i₀ → r j ≠ r i₀)
    {M : Matrix (Fin 3) (Fin 3) K} (h : M * diagonal r = diagonal r * M) {j : Fin 3}
    (hj : j ≠ i₀) : M i₀ j = 0 ∧ M j i₀ = 0 :=
  ⟨isBlockDiag_of_commute_diagonal h i₀ j fun e => hi₀ j hj e.symm,
    isBlockDiag_of_commute_diagonal h j i₀ fun e => hi₀ j hj e⟩

theorem mul_apply_simple {i₀ : Fin 3} {M N : Matrix (Fin 3) (Fin 3) K}
    (hM : ∀ j, j ≠ i₀ → M i₀ j = 0) : (M * N) i₀ i₀ = M i₀ i₀ * N i₀ i₀ := by
  rw [mul_apply]
  refine Finset.sum_eq_single i₀ (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ _) h)
  rw [hM j hj, zero_mul]

theorem conjMatrix_det_ne_zero (A x : GL (Fin 3) K) : (conjMatrix A x).det ≠ 0 := by
  have h : (conjMatrix A x) = ((A * x * A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [conjMatrix, Units.val_mul, Units.val_mul]
  rw [h]
  exact ((A * x * A⁻¹ : GL (Fin 3) K).isUnit.map (detMonoidHom (n := Fin 3) (R := K))).ne_zero

theorem isReg_of_conjMatrix_eq_diagonal {A x : GL (Fin 3) K} {r : Fin 3 → K}
    (hx : conjMatrix A x = diagonal r) (hr : Function.Injective r) :
    IsReg (x : Matrix (Fin 3) (Fin 3) K) := by
  have h := (isReg_diagonal hr).conj A⁻¹
  rw [← hx, conjMatrix, inv_inv] at h
  have e : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((A : Matrix (Fin 3) (Fin 3) K) *
      (x : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
      (A : Matrix (Fin 3) (Fin 3) K) = (x : Matrix (Fin 3) (Fin 3) K) := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rwa [e] at h

theorem isToral_of_comm [Finite K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {G : Subgroup (GL (Fin 3) K)} (hG : IsProjElem 3 G) (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x)
    (hall : ∀ x ∈ G, ∃ c : Kˣ, x ^ 3 = GeneralLinearGroup.scalar (Fin 3) (c ^ 3)) :
    IsToral G := by
  classical
  set H₁ : Set (GL (Fin 3) K) := {y | y ∈ G ∧ y ^ 3 = 1} with hH₁
  have hH₁fin : Finite H₁ := Subtype.finite
  obtain ⟨A₀, hA₀⟩ := exists_conj_diagonal hζ H₁ (fun x hx y hy => hcomm x hx.1 y hy.1)
    (fun x hx => hx.2)
  refine ⟨A₀, fun x hx i j hij => ?_⟩
  obtain ⟨c, hc⟩ := hall x hx
  have hy : GeneralLinearGroup.scalar (Fin 3) c⁻¹ * x ∈ H₁ :=
    ⟨G.mul_mem (hG.scalar_mem _) hx, pow_eq_one_of_pow_eq_scalar_pow hc⟩
  have hx' : x = GeneralLinearGroup.scalar (Fin 3) c *
      (GeneralLinearGroup.scalar (Fin 3) c⁻¹ * x) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hx']
  change conjMatrix A₀ _ i j = 0
  rw [conjMatrix_scalar_mul, Matrix.smul_apply,
    show conjMatrix A₀ _ i j = 0 from hA₀ _ hy i j hij, smul_zero]

theorem toral_or_isReg [Finite K] (hK : 3 ∣ Nat.card K - 1) {G : Subgroup (GL (Fin 3) K)}
    (hG : IsProjElem 3 G) :
    IsToral G ∨ ∀ x ∈ G, (∀ c : Kˣ, x ≠ GeneralLinearGroup.scalar (Fin 3) c) →
      IsReg (x : Matrix (Fin 3) (Fin 3) K) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hnt, x, hxG, hxs, hxr⟩ := hcon
  apply hnt
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd Nat.prime_three hK
  obtain ⟨u, hu⟩ := hG.pow_scalar x hxG
  have hcube : ∃ c : Kˣ, c ^ 3 = u := by
    by_contra hnc
    push Not at hnc
    apply hxr
    refine isReg_of_pow_three_eq (l := (u : K)) ?_ fun c hc => ?_
    · rw [← Units.val_pow_eq_pow_val, hu, GeneralLinearGroup.coe_scalar]
    · have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num)] at hc
        exact u.ne_zero hc.symm
      exact hnc (Units.mk0 c hc0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc]))
  obtain ⟨c, hc⟩ := hcube
  set y : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) c⁻¹ * x with hy
  have hyG : y ∈ G := G.mul_mem (hG.scalar_mem _) hxG
  have hy3 : y ^ 3 = 1 := pow_eq_one_of_pow_eq_scalar_pow (by rw [hu, hc])
  have hxy : x = GeneralLinearGroup.scalar (Fin 3) c * y := by
    rw [hy, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  obtain ⟨A₀, hA₀⟩ := exists_conj_diagonal hζ ({y} : Set (GL (Fin 3) K))
    (fun a ha b hb => by rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb])
    (fun a ha => by rw [Set.mem_singleton_iff.mp ha]; exact hy3)
  set r : Fin 3 → K := fun i => conjMatrix A₀ y i i with hr
  have hyd : conjMatrix A₀ y = diagonal r :=
    eq_diagonal_of_offDiag_eq_zero (hA₀ y (Set.mem_singleton y))
  have hr0 : ∀ i, r i ≠ 0 := fun i =>
    diag_ne_zero_of_eq_diagonal (D := A₀ * y * A₀⁻¹)
      (by rw [Units.val_mul, Units.val_mul]; exact hyd) i
  have hrinj : ¬ Function.Injective r := by
    intro hinj
    apply hxr
    rw [hxy, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_eq_diagonal_mul]
    exact (isReg_of_conjMatrix_eq_diagonal hyd hinj).smul (Units.ne_zero c)
  have hrconst : ∃ i j, r i ≠ r j := by
    by_contra hcst
    push Not at hcst
    apply hxs (c * Units.mk0 (r 0) (hr0 0))
    have hdiag : conjMatrix A₀ y = scalar (Fin 3) (r 0) := by
      rw [hyd, scalar_apply]
      congr 1
      funext i
      exact hcst i 0
    have hyA : y = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (r 0) (hr0 0)) := by
      apply Units.ext
      have h1 : ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * conjMatrix A₀ y *
          (A₀ : Matrix (Fin 3) (Fin 3) K) = (y : Matrix (Fin 3) (Fin 3) K) := by
        rw [conjMatrix]
        simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      rw [← h1, hdiag, GeneralLinearGroup.coe_scalar, Units.val_mk0,
        ← (scalar_commute (r 0) (fun _ => Commute.all _ _) _).eq, Matrix.mul_assoc,
        Units.inv_mul, Matrix.mul_one]
    rw [hxy, hyA, ← map_mul]
  obtain ⟨i₀, hi₀⟩ := exists_simple_entry hrinj hrconst
  have hcommy : ∀ z ∈ G, z * y = y * z := by
    intro z hz
    set χ := commChar hG hyG with hχ
    have hspec := commChar_spec hG hyG ⟨z, hz⟩
    by_cases h1 : χ ⟨z, hz⟩ = 1
    · rw [h1, map_one, one_mul] at hspec
      exact hspec.symm
    · exfalso
      apply hrinj
      have hp3 : (χ ⟨z, hz⟩ : K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, commChar_pow_eq_one hG hyG, Units.val_one]
      have hne : (χ ⟨z, hz⟩ : K) ≠ 1 := fun h => h1 (Units.ext h)
      refine injective_of_diagonal_mul_eq hr0 (conjMatrix_det_ne_zero A₀ z) hne hp3 ?_
      rw [← hyd, ← conjMatrix_mul, hspec, conjMatrix_scalar_mul, conjMatrix_mul]
  have hzero : ∀ z ∈ G, ∀ j, j ≠ i₀ → conjMatrix A₀ z i₀ j = 0 ∧ conjMatrix A₀ z j i₀ = 0 := by
    intro z hz j hj
    refine entry_eq_zero_of_simple hi₀ ?_ hj
    rw [← hyd, ← conjMatrix_mul, ← conjMatrix_mul, hcommy z hz]
  have hent0 : ∀ z ∈ G, conjMatrix A₀ z i₀ i₀ ≠ 0 := by
    intro z hz h0
    apply conjMatrix_det_ne_zero A₀ z
    refine det_eq_zero_of_row_eq_zero i₀ fun j => ?_
    by_cases hj : j = i₀
    · rw [hj, h0]
    · exact (hzero z hz j hj).1
  refine isToral_of_comm hζ hG ?_ ?_
  ·
    intro z₁ hz₁ z₂ hz₂
    obtain ⟨w, hw⟩ := hG.comm_scalar z₁ hz₁ z₂ hz₂
    have h1 := congrArg (conjMatrix A₀) hw
    rw [conjMatrix_mul, conjMatrix_scalar_mul, conjMatrix_mul] at h1
    have h2 := congrFun (congrFun h1 i₀) i₀
    rw [Matrix.smul_apply, mul_apply_simple (hzero z₁ hz₁ · · |>.1),
      mul_apply_simple (hzero z₂ hz₂ · · |>.1), smul_eq_mul] at h2
    have hw1 : (w : K) = 1 := by
      have h3 : (conjMatrix A₀ z₁ i₀ i₀ * conjMatrix A₀ z₂ i₀ i₀) * (1 - (w : K)) = 0 := by
        linear_combination h2
      exact (sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left
        (mul_ne_zero (hent0 z₁ hz₁) (hent0 z₂ hz₂)))).symm
    have hw' : w = 1 := Units.ext hw1
    rw [hw, hw', map_one, one_mul]
  ·
    intro z hz
    obtain ⟨v, hv⟩ := hG.pow_scalar z hz
    refine ⟨Units.mk0 _ (hent0 z hz), ?_⟩
    have h1 := congrArg (conjMatrix A₀) hv
    rw [conjMatrix_pow, conjMatrix_scalar] at h1
    have h2 := congrFun (congrFun h1 i₀) i₀
    rw [pow_three, mul_apply_simple (hzero z hz · · |>.1),
      mul_apply_simple (hzero z hz · · |>.1), scalar_apply, diagonal_apply_eq] at h2
    rw [hv]
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← h2]
    ring

end CFSG.StandardType.L3Three

end
