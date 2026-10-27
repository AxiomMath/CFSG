module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.StandardType

namespace OrderFiveSeven

open Matrix

variable {E : Type*} [Field E] [IsAlgClosed E] [CharP E 2] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

theorem dotProduct_mulVec_transpose (A : Matrix ι ι E) (x y : ι → E) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem exists_eigenvector_of_mem_spectrum {X : Matrix ι ι E} {θ : E}
    (hθ : θ ∈ spectrum E X) : ∃ u : ι → E, u ≠ 0 ∧ X *ᵥ u = θ • u := by
  have hnu : ¬ IsUnit (algebraMap E (Matrix ι ι E) θ - X) := (spectrum.mem_iff).mp hθ
  have hdiag : algebraMap E (Matrix ι ι E) θ = θ • (1 : Matrix ι ι E) := by
    rw [Matrix.algebraMap_eq_diagonal, Matrix.smul_one_eq_diagonal]
    simp [Pi.algebraMap_def]
  rw [hdiag] at hnu
  have hdet : (θ • (1 : Matrix ι ι E) - X).det = 0 := by
    by_contra h
    exact hnu ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
  obtain ⟨v, hv, hkill⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hkill
  exact hkill.symm

theorem pow_mulVec_eigenvector {X : Matrix ι ι E} {θ : E} {u : ι → E}
    (hmul : X *ᵥ u = θ • u) (n : ℕ) : X ^ n *ᵥ u = θ ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hmul, smul_smul,
        ← pow_succ]

theorem pow_eq_one_of_mem_spectrum {X : Matrix ι ι E} {θ : E} {m : ℕ}
    (hθ : θ ∈ spectrum E X) (hX : X ^ m = 1) : θ ^ m = 1 := by
  obtain ⟨u, hu, hmul⟩ := exists_eigenvector_of_mem_spectrum hθ
  have hpow := pow_mulVec_eigenvector hmul m
  rw [hX, Matrix.one_mulVec] at hpow
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  have h := congrFun hpow i
  simp only [Pi.smul_apply, smul_eq_mul] at h
  exact (mul_right_cancel₀ hi (by rw [one_mul]; exact h)).symm

theorem pow_inj_of_orderOf {θ : E} {n : ℕ} (hx : IsOfFinOrder θ) (h : orderOf θ = n)
    (i j : ℕ) (hi : i < n) (hj : j < n) (hij : θ ^ i = θ ^ j) : i = j := by
  have hp := hx.pow_eq_pow_iff_modEq.mp hij
  rw [h] at hp
  exact hp.eq_of_lt_of_lt hi hj

theorem one_add_sq (N : Matrix ι ι E) : (1 + N) ^ 2 = 1 + N ^ 2 := by
  have h2E : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have h2 : (2 : Matrix ι ι E) = 0 := by
    rw [show (2 : Matrix ι ι E) = algebraMap E (Matrix ι ι E) (2 : E) from
      (map_natCast (algebraMap E (Matrix ι ι E)) 2).symm, h2E, map_zero]
  have h : (1 + N) ^ 2 = 1 + N ^ 2 + 2 * N := by noncomm_ring
  rw [h, show (2 : Matrix ι ι E) * N = 0 from by rw [h2, zero_mul], add_zero]

theorem sq_mem_spectrum_of_conj_sq {X Y : Matrix ι ι E} (hY : IsUnit Y)
    (hXY : Y * X = X ^ 2 * Y) {θ : E} (hθ : θ ∈ spectrum E X) : θ ^ 2 ∈ spectrum E X := by
  obtain ⟨u, rfl⟩ := hY
  have hX2 : X ^ 2 = (↑u : Matrix ι ι E) * X * (↑(u⁻¹) : Matrix ι ι E) := by
    rw [hXY, mul_assoc]
    simp
  have hspec : spectrum E (X ^ 2) = spectrum E X := by
    rw [hX2, spectrum.units_conjugate]
  rw [← hspec]
  exact spectrum.pow_mem_pow X 2 hθ

theorem card_spectrum_le (X : Matrix ι ι E) :
    (spectrum E X).Finite ∧ (spectrum E X).ncard ≤ Fintype.card ι := by
  classical
  have hchar_ne : X.charpoly ≠ 0 := X.charpoly_monic.ne_zero
  have hset : spectrum E X = (X.charpoly.roots.toFinset : Set E) := by
    ext r
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_roots hchar_ne]
  constructor
  · rw [hset]; exact Finset.finite_toSet _
  · rw [hset, Set.ncard_coe_finset]
    calc X.charpoly.roots.toFinset.card ≤ X.charpoly.roots.card := Multiset.toFinset_card_le _
      _ = X.charpoly.natDegree :=
          (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits X.charpoly))
      _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim X

theorem eq_one_of_spectrum_subset_one {m : ℕ} (hm : Odd m) {X : Matrix ι ι E} (hX : X ^ m = 1)
    (hs : spectrum E X ⊆ {1}) : X = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hroot : ∀ r : E, X.charpoly.IsRoot r → r = 1 := by
    intro r hr
    have hmem : r ∈ spectrum E X := (Matrix.mem_spectrum_iff_isRoot_charpoly).mpr hr
    simpa using hs hmem
  have hnil : IsNilpotent (X - 1) := by
    refine ⟨X.charpoly.roots.card, ?_⟩
    have hfac : X.charpoly =
        (X.charpoly.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod :=
      (IsAlgClosed.splits X.charpoly).eq_prod_roots_of_monic X.charpoly_monic
    have hmap : X.charpoly.roots.map (fun r => Polynomial.X - Polynomial.C r) =
        X.charpoly.roots.map (fun _ => Polynomial.X - Polynomial.C 1) := by
      apply Multiset.map_congr rfl
      intro r hr
      rw [hroot r ((Polynomial.mem_roots X.charpoly_monic.ne_zero).mp hr)]
    have hpow : X.charpoly = (Polynomial.X - Polynomial.C 1) ^ X.charpoly.roots.card := by
      calc X.charpoly = (X.charpoly.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod :=
            hfac
        _ = (X.charpoly.roots.map (fun _ => Polynomial.X - Polynomial.C 1)).prod := by rw [hmap]
        _ = (Multiset.replicate X.charpoly.roots.card
              (Polynomial.X - Polynomial.C 1)).prod := by rw [Multiset.map_const']
        _ = (Polynomial.X - Polynomial.C 1) ^ X.charpoly.roots.card := Multiset.prod_replicate _ _
    have hCH : Polynomial.aeval X X.charpoly = 0 := Matrix.aeval_self_charpoly X
    rw [hpow] at hCH
    simpa using hCH
  obtain ⟨d, hd⟩ := hnil
  have hiter : ∀ k, (1 + (X - 1)) ^ (2 ^ k) = 1 + (X - 1) ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h1 : (1 + (X - 1)) ^ (2 ^ (k + 1)) = ((1 + (X - 1)) ^ (2 ^ k)) ^ 2 := by
          rw [pow_succ, pow_mul]
        rw [h1, ih, one_add_sq, ← pow_mul, pow_succ]
  have hX2d : X ^ (2 ^ d) = 1 := by
    have hpowzero : (X - 1) ^ (2 ^ d) = 0 :=
      pow_eq_zero_of_le (Nat.lt_two_pow_self (n := d)).le hd
    rw [show X = 1 + (X - 1) from by abel, hiter d, hpowzero, add_zero]
  have h1 : orderOf X ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hX
  have h2 : orderOf X ∣ 2 ^ d := orderOf_dvd_iff_pow_eq_one.mpr hX2d
  have hcop : Nat.Coprime m (2 ^ d) := hm.coprime_two_right.pow_right d
  have hg : Nat.gcd m (2 ^ d) = 1 := hcop.gcd_eq_one
  have hdvd : orderOf X ∣ 1 := by rw [← hg]; exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem eq_one_of_pow_five_of_card_le_three (hι : Fintype.card ι ≤ 3) {X Y : Matrix ι ι E}
    (hY : IsUnit Y) (hXY : Y * X = X ^ 2 * Y) (hX : X ^ 5 = 1) : X = 1 := by
  by_contra hne
  have hnotsub : ¬ spectrum E X ⊆ {1} := by
    intro hs
    exact hne (eq_one_of_spectrum_subset_one (m := 5) (by decide) hX hs)
  rw [Set.not_subset] at hnotsub
  obtain ⟨θ, hθ, hθnot⟩ := hnotsub
  have hθne : θ ≠ 1 := by simpa using hθnot
  have hθ5 : θ ^ 5 = 1 := pow_eq_one_of_mem_spectrum hθ hX
  have hord : orderOf θ = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime hθ5 hθne
  have hfinθ : IsOfFinOrder θ := isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, hθ5⟩
  have hinj := pow_inj_of_orderOf hfinθ hord
  have hθ2 : θ ^ 2 ∈ spectrum E X := sq_mem_spectrum_of_conj_sq hY hXY hθ
  have hθ4 : θ ^ 4 ∈ spectrum E X := by
    have := sq_mem_spectrum_of_conj_sq hY hXY hθ2
    rwa [show (θ ^ 2) ^ 2 = θ ^ 4 from by rw [← pow_mul]] at this
  have hθ3 : θ ^ 3 ∈ spectrum E X := by
    have h8 : θ ^ 8 = θ ^ 3 := by rw [show (8 : ℕ) = 5 + 3 from rfl, pow_add, hθ5, one_mul]
    have := sq_mem_spectrum_of_conj_sq hY hXY hθ4
    rwa [show (θ ^ 4) ^ 2 = θ ^ 3 from by rw [← pow_mul]; exact h8] at this
  have h12 : θ ^ 1 ≠ θ ^ 2 :=
    fun h => absurd (hinj (1) (2) (by norm_num) (by norm_num) h) (by norm_num)
  have h13 : θ ^ 1 ≠ θ ^ 3 :=
    fun h => absurd (hinj (1) (3) (by norm_num) (by norm_num) h) (by norm_num)
  have h14 : θ ^ 1 ≠ θ ^ 4 :=
    fun h => absurd (hinj (1) (4) (by norm_num) (by norm_num) h) (by norm_num)
  have h23 : θ ^ 2 ≠ θ ^ 3 :=
    fun h => absurd (hinj (2) (3) (by norm_num) (by norm_num) h) (by norm_num)
  have h24 : θ ^ 2 ≠ θ ^ 4 :=
    fun h => absurd (hinj (2) (4) (by norm_num) (by norm_num) h) (by norm_num)
  have h43 : θ ^ 4 ≠ θ ^ 3 :=
    fun h => absurd (hinj (4) (3) (by norm_num) (by norm_num) h) (by norm_num)
  have hsub : ({θ ^ 1, θ ^ 2, θ ^ 4, θ ^ 3} : Set E) ⊆ spectrum E X := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simpa using hθ
    · exact hθ2
    · exact hθ4
    · exact hθ3
  have hSncard : ({θ ^ 1, θ ^ 2, θ ^ 4, θ ^ 3} : Set E).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (s := ({θ ^ 2, θ ^ 4, θ ^ 3} : Set E)) (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h12, h14, h13⟩)]
    rw [Set.ncard_insert_of_notMem (s := ({θ ^ 4, θ ^ 3} : Set E)) (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h24, h23⟩)]
    rw [Set.ncard_insert_of_notMem (s := ({θ ^ 3} : Set E)) (by simpa using h43)]
    rw [Set.ncard_singleton]
  have hSle : ({θ ^ 1, θ ^ 2, θ ^ 4, θ ^ 3} : Set E).ncard ≤ (spectrum E X).ncard :=
    Set.ncard_le_ncard hsub (card_spectrum_le X).1
  rw [hSncard] at hSle
  have hcard := (card_spectrum_le X).2
  omega

theorem inv_mem_spectrum_of_form (σ : E ≃+* E)
    (hσ : ∀ η : E, η ^ 7 = 1 → ∃ k : ℕ, σ η = η ^ 2 ^ k) {G : Matrix ι ι E} (hG : IsUnit G)
    {X Y : Matrix ι ι E} (hY : IsUnit Y) (hXY : Y * X = X ^ 2 * Y) (hX : X ^ 7 = 1)
    (hform : Xᵀ * G * X.map σ = G) {θ : E} (hθ : θ ∈ spectrum E X) : θ⁻¹ ∈ spectrum E X := by
  obtain ⟨u, hu_ne, hmul⟩ := exists_eigenvector_of_mem_spectrum hθ
  have hθ7 : θ ^ 7 = 1 := pow_eq_one_of_mem_spectrum hθ hX
  have hθne : θ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 7 ≠ 0)] at hθ7
    exact zero_ne_one hθ7
  set w0 : ι → E := Gᵀ *ᵥ u with hw0def
  have hGt_det : Gᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG)
  have hw0 : w0 ≠ 0 := by
    intro h0
    exact hu_ne (Matrix.eq_zero_of_mulVec_eq_zero hGt_det h0)
  have hmul_dot : ∀ z : ι → E, u ⬝ᵥ (G *ᵥ z) = w0 ⬝ᵥ z := by
    intro z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hσmul : ∀ v : ι → E, σ ∘ (X *ᵥ v) = (X.map σ) *ᵥ (σ ∘ v) := by
    intro v
    ext i
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      map_sum, map_mul]
  have hinv : ∀ v : ι → E,
      u ⬝ᵥ (G *ᵥ (σ ∘ v)) = (X *ᵥ u) ⬝ᵥ (G *ᵥ (σ ∘ (X *ᵥ v))) := by
    intro v
    rw [hσmul v]
    rw [dotProduct_mulVec_transpose X u (G *ᵥ ((X.map σ) *ᵥ (σ ∘ v)))]
    congr 1
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hform]
  have hrel : ∀ v : ι → E,
      w0 ⬝ᵥ ((X.map σ) *ᵥ (σ ∘ v)) = θ⁻¹ * (w0 ⬝ᵥ (σ ∘ v)) := by
    intro v
    have h := hinv v
    rw [hmul, smul_dotProduct, hσmul v] at h
    rw [hmul_dot (σ ∘ v), hmul_dot ((X.map σ) *ᵥ (σ ∘ v))] at h
    rw [h, smul_eq_mul, inv_mul_cancel_left₀ hθne]
  have hfin : ∀ z : ι → E, ((X.map σ)ᵀ *ᵥ w0) ⬝ᵥ z = (θ⁻¹ • w0) ⬝ᵥ z := by
    intro z
    have hz := hrel (fun i => σ.symm (z i))
    have hcomp : (σ ∘ fun i => σ.symm (z i)) = z := by
      funext i; simp
    rw [hcomp] at hz
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at hz
    rw [smul_dotProduct, smul_eq_mul]
    exact hz
  have hkey : (X.map σ)ᵀ *ᵥ w0 = θ⁻¹ • w0 := by
    apply (dotProductEquiv E ι).injective
    apply LinearMap.ext
    intro z
    exact hfin z
  have hspec_dual : θ⁻¹ ∈ spectrum E ((X.map σ)ᵀ) := by
    rw [spectrum.mem_iff]
    intro hunit
    have hdet : (algebraMap E (Matrix ι ι E) θ⁻¹ - (X.map σ)ᵀ).det ≠ 0 :=
      isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
    have hdiag : algebraMap E (Matrix ι ι E) θ⁻¹ = θ⁻¹ • (1 : Matrix ι ι E) := by
      rw [Matrix.algebraMap_eq_diagonal, Matrix.smul_one_eq_diagonal]
      simp [Pi.algebraMap_def]
    have hkill : (algebraMap E (Matrix ι ι E) θ⁻¹ - (X.map σ)ᵀ) *ᵥ w0 = 0 := by
      rw [hdiag, sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hkey, sub_self]
    exact hw0 (Matrix.eq_zero_of_mulVec_eq_zero hdet hkill)
  have hroot : ((X.charpoly).map σ).IsRoot (θ⁻¹) := by
    have h := (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hspec_dual
    rw [Matrix.charpoly_transpose] at h
    have h2 : (X.map σ).charpoly = X.charpoly.map σ := Matrix.charpoly_map X (σ : E →+* E)
    rwa [h2] at h
  set η : E := σ.symm (θ⁻¹) with hηdef
  have hηmem : η ∈ spectrum E X := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
    refine (Polynomial.isRoot_map_iff (f := (σ : E →+* E)) σ.injective).mp ?_
    simpa [η, σ.apply_symm_apply] using hroot
  have hη7 : η ^ 7 = 1 := by
    have hσθ : (σ.symm θ) ^ 7 = 1 := by
      have := congrArg σ.symm hθ7
      simpa [map_pow] using this
    have hηeq : η = (σ.symm θ)⁻¹ := by
      show σ.symm (θ⁻¹) = (σ.symm θ)⁻¹
      rw [map_inv₀]
    rw [hηeq, inv_pow, hσθ, inv_one]
  have hpow_mem : ∀ k : ℕ, η ^ (2 ^ k) ∈ spectrum E X := by
    intro k
    induction k with
    | zero => simpa using hηmem
    | succ k ih =>
        have h2 : η ^ 2 ^ (k + 1) = (η ^ 2 ^ k) ^ 2 := by rw [pow_succ, ← pow_mul]
        rw [h2]
        exact sq_mem_spectrum_of_conj_sq hY hXY ih
  obtain ⟨k, hk⟩ := hσ η hη7
  have : θ⁻¹ = η ^ (2 ^ k) := by rw [← hk, σ.apply_symm_apply]
  rw [this]
  exact hpow_mem k

theorem eq_one_of_pow_seven_of_form (σ : E ≃+* E)
    (hσ : ∀ η : E, η ^ 7 = 1 → ∃ k : ℕ, σ η = η ^ 2 ^ k) {G : Matrix ι ι E} (hG : IsUnit G)
    (hι : Fintype.card ι ≤ 5) {X Y : Matrix ι ι E} (hY : IsUnit Y) (hXY : Y * X = X ^ 2 * Y)
    (hX : X ^ 7 = 1) (hform : Xᵀ * G * X.map σ = G) : X = 1 := by
  classical
  by_contra hne
  have hnotsub : ¬ spectrum E X ⊆ {1} := by
    intro hs
    exact hne (eq_one_of_spectrum_subset_one (m := 7) (by decide) hX hs)
  rw [Set.not_subset] at hnotsub
  obtain ⟨θ, hθ, hθnot⟩ := hnotsub
  have hθne : θ ≠ 1 := by simpa using hθnot
  have hθ7 : θ ^ 7 = 1 := pow_eq_one_of_mem_spectrum hθ hX
  have hord : orderOf θ = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    exact orderOf_eq_prime hθ7 hθne
  have hfinθ : IsOfFinOrder θ := isOfFinOrder_iff_pow_eq_one.mpr ⟨7, by norm_num, hθ7⟩
  have hinj := pow_inj_of_orderOf hfinθ hord
  have hθ2 : θ ^ 2 ∈ spectrum E X := sq_mem_spectrum_of_conj_sq hY hXY hθ
  have hθ4 : θ ^ 4 ∈ spectrum E X := by
    have := sq_mem_spectrum_of_conj_sq hY hXY hθ2
    rwa [show (θ ^ 2) ^ 2 = θ ^ 4 from by rw [← pow_mul]] at this
  have hθ6 : θ ^ 6 ∈ spectrum E X := by
    have := inv_mem_spectrum_of_form σ hσ hG hY hXY hX hform hθ
    have he : θ⁻¹ = θ ^ 6 := by
      have h6 : θ ^ 6 * θ = 1 := by rw [← pow_succ]; exact hθ7
      exact (eq_inv_of_mul_eq_one_left h6).symm
    rwa [he] at this
  have hθ5 : θ ^ 5 ∈ spectrum E X := by
    have := inv_mem_spectrum_of_form σ hσ hG hY hXY hX hform hθ2
    have he : (θ ^ 2)⁻¹ = θ ^ 5 := by
      have h5 : θ ^ 5 * θ ^ 2 = 1 := by rw [← pow_add]; norm_num; exact hθ7
      exact (eq_inv_of_mul_eq_one_left h5).symm
    rwa [he] at this
  have hθ3 : θ ^ 3 ∈ spectrum E X := by
    have := inv_mem_spectrum_of_form σ hσ hG hY hXY hX hform hθ4
    have he : (θ ^ 4)⁻¹ = θ ^ 3 := by
      have h3 : θ ^ 3 * θ ^ 4 = 1 := by rw [← pow_add]; norm_num; exact hθ7
      exact (eq_inv_of_mul_eq_one_left h3).symm
    rwa [he] at this
  let g : Fin 6 → ℕ := ![1, 2, 4, 6, 5, 3]
  let f : Fin 6 → E := fun i => θ ^ g i
  have hg_lt : ∀ i, g i < 7 := by decide
  have hg_inj : Function.Injective g := by decide
  have hfinj : Function.Injective f := by
    intro i j hij
    exact hg_inj (hinj (g i) (g j) (hg_lt i) (hg_lt j) hij)
  have hcard : (Finset.univ.image f).card = 6 := by
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
  have hsub : ((Finset.univ.image f : Finset E) : Set E) ⊆ spectrum E X := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    fin_cases i
    · simpa [f, g] using hθ
    · simpa [f, g] using hθ2
    · simpa [f, g] using hθ4
    · simpa [f, g] using hθ6
    · simpa [f, g] using hθ5
    · simpa [f, g] using hθ3
  have hSle : ((Finset.univ.image f : Finset E) : Set E).ncard ≤ (spectrum E X).ncard :=
    Set.ncard_le_ncard hsub (card_spectrum_le X).1
  rw [Set.ncard_coe_finset, hcard] at hSle
  have hcard' := (card_spectrum_le X).2
  omega

end OrderFiveSeven

end CFSG.StandardType
