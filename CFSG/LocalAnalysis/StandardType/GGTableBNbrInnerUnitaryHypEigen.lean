module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCount
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityMatrix
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  TableB

variable {n r p : ℕ} {K : Type} [Field K]

theorem bar_eq_self_of_pow_eq_one (h : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n - 1) {x : K}
    (hx : x ^ p = 1) : h.bar x = x := by
  obtain ⟨m, hm⟩ := hpq
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [h.bar_apply, ← Nat.sub_add_cancel h2n, hm, pow_add, pow_mul, hx, one_pow, one_mul,
    pow_one]

theorem exists_primitiveRoot_of_dvd_two_pow_sub_one (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1) : ∃ ζ : K, IsPrimitiveRoot ζ p := by
  haveI : Finite K := h.finite
  have hpK : p ∣ Nat.card K - 1 := by
    have h2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [show 2 * n = n * 2 by ring, pow_mul]
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ n) 1
    rw [h.card, h2, hfac]
    exact dvd_mul_of_dvd_left hpq _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hpK)
  exact ⟨u, IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)⟩

structure HypEigenframe (h : UnitaryFieldData 2 n K) (p : ℕ) (E : Subgroup (hypSU h r 0)) where
  N : GL (HypIndex r 0) K
  χ : E →* (HypIndex r 0 → Kˣ)
  inj : Function.Injective χ
  pow : ∀ (x : E) (i : HypIndex r 0), χ x i ^ p = 1
  conj : ∀ x : E,
    (((x : hypSU h r 0) : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) *
        (N : Matrix (HypIndex r 0) (HypIndex r 0) K) =
      (N : Matrix (HypIndex r 0) (HypIndex r 0) K) * diagonal fun i => ((χ x i : Kˣ) : K)

@[expose] noncomputable def HypEigenframe.gram {h : UnitaryFieldData 2 n K}
    {E : Subgroup (hypSU h r 0)} (F : HypEigenframe h p E) :
    Matrix (HypIndex r 0) (HypIndex r 0) K :=
  (((F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar)ᵀ * hypGram r 0 K) *
    (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K)

theorem nonempty_hypEigenframe (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hpq : p ∣ 2 ^ n - 1)
    (E : Subgroup (hypSU h r 0)) (hE : IsElemAbelian p E) : Nonempty (HypEigenframe h p E) := by
  classical
  haveI : Finite K := h.finite
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let φ : E →* GL (HypIndex r 0) K := (hypSU h r 0).subtype.comp E.subtype
  let S : Set (GL (HypIndex r 0) K) := Set.range φ
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    exact congrArg (fun z : hypSU h r 0 => (z : GL (HypIndex r 0) K))
      (TableB.IsElemAbelian.comm hE a.2 b.2)
  have hpow : ∀ x ∈ S, x ^ p = 1 := by
    rintro x ⟨a, rfl⟩
    exact congrArg (fun z : hypSU h r 0 => (z : GL (HypIndex r 0) K)) (hE.2 a a.2)
  obtain ⟨A, hA⟩ := TypeA.PGLTor.exists_conj_diagonal hζ S hcomm hpow
  let Dg : E →* GL (HypIndex r 0) K := (MulAut.conj A).toMonoidHom.comp φ
  let D : E → Matrix (HypIndex r 0) (HypIndex r 0) K := fun x => (Dg x : Matrix _ _ K)
  have hDdiag : ∀ x : E, D x = diagonal (fun i => D x i i) := by
    intro x
    ext i j
    by_cases hij : i = j
    · subst hij; rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]
      exact hA (φ x) (Set.mem_range.mpr ⟨x, rfl⟩) i j hij
  have hunit : ∀ x : E, IsUnit (D x) := by
    intro x
    exact IsUnit.mul (IsUnit.mul ⟨A, rfl⟩ ⟨φ x, rfl⟩) ⟨A⁻¹, rfl⟩
  have hd_ne : ∀ (x : E) (i : HypIndex r 0), D x i i ≠ 0 := by
    intro x i
    have h1 : IsUnit (diagonal (fun i => D x i i)) := hDdiag x ▸ hunit x
    have h2 : IsUnit ((fun i => D x i i) i) := (Matrix.isUnit_diagonal.mp h1).apply i
    exact isUnit_iff_ne_zero.mp h2
  have hDmul : ∀ x y : E, D (x * y) = D x * D y := by
    intro x y
    simp only [D, map_mul, Units.val_mul]
  have hDmul_apply : ∀ (x y : E) (i : HypIndex r 0),
      D (x * y) i i = D x i i * D y i i := by
    intro x y i
    rw [hDmul]
    conv_lhs => rw [hDdiag x, hDdiag y]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
  have hD1 : D 1 = 1 := by
    show ((Dg 1 : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) = 1
    rw [map_one, Units.val_one]
  let χ : E →* (HypIndex r 0 → Kˣ) :=
    { toFun := fun x i => Units.mk0 (D x i i) (hd_ne x i)
      map_one' := by
        ext i
        show D 1 i i = 1
        rw [hD1, Matrix.one_apply_eq]
      map_mul' := by
        intro x y
        ext i
        show D (x * y) i i = D x i i * D y i i
        exact hDmul_apply x y i }
  have hχpow : ∀ (x : E) (i : HypIndex r 0), χ x i ^ p = 1 := by
    intro x i
    apply Units.ext
    show (D x i i) ^ p = 1
    have hxp : x ^ p = 1 := Subtype.ext (by simpa using hE.2 (x : hypSU h r 0) x.2)
    have hDgp : Dg x ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hDpow : D x ^ p = 1 := by
      show ((Dg x : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) ^ p = 1
      rw [← Units.val_pow_eq_pow_val, hDgp, Units.val_one]
    have hdiag : diagonal (fun i => D x i i ^ p) = (1 : Matrix _ _ K) := by
      have h2 : diagonal (fun i => D x i i) ^ p = 1 := by
        rw [← hDdiag x, hDpow]
      rw [Matrix.diagonal_pow] at h2
      exact h2
    have := congrFun (congrFun hdiag i) i
    simpa [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using this
  have hDg_diag : ∀ x : E, (Dg x : Matrix (HypIndex r 0) (HypIndex r 0) K) =
      diagonal (fun i => ((χ x i : Kˣ) : K)) := by
    intro x
    have hfun : (fun i => ((χ x i : Kˣ) : K)) = fun i => D x i i := rfl
    rw [hfun]
    exact hDdiag x
  have hinj : Function.Injective χ := by
    intro x y hxy
    have hDg : Dg x = Dg y := by
      apply Units.ext
      rw [hDg_diag x, hDg_diag y, hxy]
    have hφ : φ x = φ y := by
      apply (MulAut.conj A).injective
      exact hDg
    exact Subtype.ext (Subtype.ext hφ)
  refine ⟨A⁻¹, χ, hinj, hχpow, ?_⟩
  intro x
  have hgl : (A⁻¹ : GL (HypIndex r 0) K) * Dg x = φ x * A⁻¹ := by
    show (A⁻¹ : GL (HypIndex r 0) K) * (A * φ x * A⁻¹) = φ x * A⁻¹
    group
  have hmat : ((A⁻¹ : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) *
        ((Dg x : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) =
      ((φ x : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) *
        ((A⁻¹ : GL (HypIndex r 0) K) : Matrix (HypIndex r 0) (HypIndex r 0) K) := by
    simpa only [Units.val_mul] using
      congrArg (fun u : GL (HypIndex r 0) K => (u : Matrix (HypIndex r 0) (HypIndex r 0) K)) hgl
  rw [← hDg_diag x]
  exact hmat.symm

theorem HypEigenframe.chi_mul_chi_eq_one {h : UnitaryFieldData 2 n K} (hpq : p ∣ 2 ^ n - 1)
    {E : Subgroup (hypSU h r 0)} (F : HypEigenframe h p E) {i j : HypIndex r 0}
    (hij : F.gram i j ≠ 0) (x : E) : F.χ x i * F.χ x j = 1 := by
  let N : Matrix (HypIndex r 0) (HypIndex r 0) K := (F.N : Matrix _ _ K)
  let xm : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    (((x : hypSU h r 0) : GL (HypIndex r 0) K) : Matrix _ _ K)
  let D : Matrix (HypIndex r 0) (HypIndex r 0) K :=
    diagonal (fun i => ((F.χ x i : Kˣ) : K))
  have hconj : xm * N = N * D := F.conj x
  have h1 : (N.map h.bar)ᵀ * (xm.map h.bar)ᵀ = (D.map h.bar)ᵀ * (N.map h.bar)ᵀ := by
    have hh := congrArg (fun M : Matrix (HypIndex r 0) (HypIndex r 0) K => (M.map h.bar)ᵀ) hconj
    rwa [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul] at hh
  have hxJ : (xm.map h.bar)ᵀ * hypGram r 0 K * xm = hypGram r 0 K :=
    (mem_hypSU.mp (x : hypSU h r 0).2).1
  have hmid : (D.map h.bar)ᵀ * ((N.map h.bar)ᵀ * hypGram r 0 K * N) * D =
      (N.map h.bar)ᵀ * ((xm.map h.bar)ᵀ * hypGram r 0 K * xm) * N := by
    calc (D.map h.bar)ᵀ * ((N.map h.bar)ᵀ * hypGram r 0 K * N) * D
        = ((D.map h.bar)ᵀ * (N.map h.bar)ᵀ) * hypGram r 0 K * (N * D) := by
          simp only [Matrix.mul_assoc]
      _ = ((N.map h.bar)ᵀ * (xm.map h.bar)ᵀ) * hypGram r 0 K * (xm * N) := by
          rw [← h1, ← hconj]
      _ = (N.map h.bar)ᵀ * ((xm.map h.bar)ᵀ * hypGram r 0 K * xm) * N := by
          simp only [Matrix.mul_assoc]
  have hkey : (D.map h.bar)ᵀ * F.gram * D = F.gram := by
    show (D.map h.bar)ᵀ * ((N.map h.bar)ᵀ * hypGram r 0 K * N) * D =
      (N.map h.bar)ᵀ * hypGram r 0 K * N
    calc (D.map h.bar)ᵀ * ((N.map h.bar)ᵀ * hypGram r 0 K * N) * D
        = (N.map h.bar)ᵀ * ((xm.map h.bar)ᵀ * hypGram r 0 K * xm) * N := hmid
      _ = (N.map h.bar)ᵀ * hypGram r 0 K * N := by rw [hxJ]
  have hentry : ((D.map h.bar)ᵀ * F.gram * D) i j =
      h.bar ((F.χ x i : Kˣ) : K) * F.gram i j * ((F.χ x j : Kˣ) : K) := by
    simp only [D, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hgram_eq : h.bar ((F.χ x i : Kˣ) : K) * F.gram i j * ((F.χ x j : Kˣ) : K) =
      F.gram i j := by
    rw [← hentry, hkey]
  have hbar_di : h.bar ((F.χ x i : Kˣ) : K) = ((F.χ x i : Kˣ) : K) := by
    refine bar_eq_self_of_pow_eq_one h hpq ?_
    have := congrArg (fun u : Kˣ => (u : K)) (F.pow x i)
    simpa [Units.val_pow_eq_pow_val] using this
  exact Units.ext (by
    rw [Units.val_mul, Units.val_one, ← hbar_di]
    have h2 : (h.bar ((F.χ x i : Kˣ) : K) * ((F.χ x j : Kˣ) : K)) * F.gram i j =
        1 * F.gram i j := by
      rw [one_mul]
      calc (h.bar ((F.χ x i : Kˣ) : K) * ((F.χ x j : Kˣ) : K)) * F.gram i j
          = h.bar ((F.χ x i : Kˣ) : K) * F.gram i j * ((F.χ x j : Kˣ) : K) := by ring
        _ = F.gram i j := hgram_eq
    exact mul_right_cancel₀ hij h2)

theorem HypEigenframe.exists_antisymm_perm {h : UnitaryFieldData 2 n K} (hpq : p ∣ 2 ^ n - 1)
    {E : Subgroup (hypSU h r 0)} (F : HypEigenframe h p E) :
    ∃ τ : Equiv.Perm (HypIndex r 0), (∀ i, F.gram i (τ i) ≠ 0) ∧
      ∀ (x : E) (i : HypIndex r 0), F.χ x (τ i) = (F.χ x i)⁻¹ := by
  have hdet : F.gram.det ≠ 0 := by
    have hN : (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero F.N
    have hNmap : ((F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar).det ≠ 0 := by
      have hmap := (RingHom.map_det h.bar (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K)).symm
      rw [show h.bar.mapMatrix (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K) =
        (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar from rfl] at hmap
      rw [hmap]
      intro hz
      exact hN (h.bar.injective (by rw [hz, map_zero]))
    show ((((F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar)ᵀ * hypGram r 0 K) *
      (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K)).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hNmap det_hypGram_ne_zero) hN
  obtain ⟨σ, hσ⟩ := exists_perm_ne_zero_of_det_ne_zero hdet
  have hHerm : (F.gram.map h.bar)ᵀ = F.gram := by
    have hstarN : ((((F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar)ᵀ).map h.bar)ᵀ =
        (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K) := by
      rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_map,
        show h.bar ∘ h.bar = id from funext h.bar_bar, Matrix.map_id]
    show (((((F.N : Matrix (HypIndex r 0) (HypIndex r 0) K).map h.bar)ᵀ * hypGram r 0 K) *
      (F.N : Matrix (HypIndex r 0) (HypIndex r 0) K)).map h.bar)ᵀ = F.gram
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      hypGram_conjTranspose, hstarN]
    simp only [HypEigenframe.gram, Matrix.mul_assoc]
  refine ⟨σ, ?_, ?_⟩
  · intro i
    have hpos := hσ i
    intro hzero
    apply hpos
    have hentry := congrFun (congrFun hHerm (σ i)) i
    rw [Matrix.transpose_apply, Matrix.map_apply, hzero, map_zero] at hentry
    exact hentry.symm
  · intro x i
    exact eq_inv_of_mul_eq_one_left (HypEigenframe.chi_mul_chi_eq_one hpq F (hσ i) x)

theorem card_le_pow_hypSU (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) (E : Subgroup (hypSU h r 0)) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ r := by
  obtain ⟨F⟩ := nonempty_hypEigenframe h hp hpq E hE
  obtain ⟨τ, hτ1, hτ2⟩ := F.exists_antisymm_perm hpq
  have hE' : ∀ t ∈ F.χ.range, ∀ i, t i ^ p = 1 := by
    rintro t ⟨x, rfl⟩ i
    exact F.pow x i
  have hτ' : ∀ t ∈ F.χ.range, ∀ i, t (τ i) = (t i)⁻¹ := by
    rintro t ⟨x, rfl⟩ i
    exact hτ2 x i
  have hcard := card_le_pow_of_inv_perm hp hp2 τ F.χ.range hE' hτ'
  have hEmap : Nat.card E = Nat.card F.χ.range :=
    Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv
  have hcardι : Fintype.card (HypIndex r 0) / 2 = r := by
    have h2 : Fintype.card (HypIndex r 0) = 2 * r := by
      simp only [HypIndex, Fintype.card_sum, Fintype.card_fin]
      omega
    rw [h2]
    omega
  rw [hEmap]
  rw [hcardι] at hcard
  exact hcard

theorem HypEigenframe.exists_gram_monomial {h : UnitaryFieldData 2 n K} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) {E : Subgroup (hypSU h r 0)} (F : HypEigenframe h p E)
    (hcard : p ^ r ≤ Nat.card E) :
    ∃ τ : Equiv.Perm (HypIndex r 0), (∀ i, τ i ≠ i) ∧ (∀ i, τ (τ i) = i) ∧
      (∀ i j, F.gram i j ≠ 0 → j = τ i) ∧ ∀ i, F.gram i (τ i) ≠ 0 := by
  obtain ⟨τ₀, hτ₀pos, hτ₀inv⟩ := F.exists_antisymm_perm hpq
  have hEmap : Nat.card E = Nat.card F.χ.range :=
    Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv
  have hcard' : p ^ r ≤ Nat.card F.χ.range := by rw [← hEmap]; exact hcard
  have hE' : ∀ t ∈ F.χ.range, ∀ i, t i ^ p = 1 := by
    rintro t ⟨x, rfl⟩ i
    exact F.pow x i
  have hτ' : ∀ t ∈ F.χ.range, ∀ i, t (τ₀ i) = (t i)⁻¹ := by
    rintro t ⟨x, rfl⟩ i
    exact hτ₀inv x i
  have hcardι : Fintype.card (HypIndex r 0) = 2 * r := by
    simp only [HypIndex, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨hτ1, hτ2, hτall⟩ :=
    fpf_involution_of_card_ge hp hp2 hcardι τ₀ F.χ.range hE' hτ' hcard'
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  let u : Kˣ := (hζ.isUnit hp.ne_zero).unit
  have hu : orderOf u = p :=
    (IsPrimitiveRoot.isUnit_unit (n := p) hp.ne_zero hζ).eq_orderOf.symm
  refine ⟨τ₀, hτ1, hτ2, ?_, hτ₀pos⟩
  intro i j hij
  by_contra hj
  obtain ⟨t, htpow, htsymm, htij⟩ :=
    exists_mem_of_fpf_involution hp hp2 hu τ₀ hτ1 hτ2 i j hj
  obtain ⟨x, hx⟩ := hτall t htpow htsymm
  rw [← hx] at htij
  exact htij (HypEigenframe.chi_mul_chi_eq_one hpq F hij x)

end CFSG.StandardType

end
