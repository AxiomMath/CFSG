module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVSp64Lin
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV

open Matrix Polynomial

variable {L : Type*} [Field L]

section Eig

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalar_mulVec_eq (c : L) (x : ι → L) : scalar ι c *ᵥ x = c • x := by
  funext i
  rw [scalar_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

theorem exists_eigenvalue_ne_one_of_pow_eq_one [IsAlgClosed L] {p : ℕ} (hp : (p : L) ≠ 0)
    {B : Matrix ι ι L} (hBp : B ^ p = 1) (hB1 : B ≠ 1) :
    ∃ μ : L, ∃ v : ι → L, v ≠ 0 ∧ B *ᵥ v = μ • v ∧ μ ≠ 1 := by
  set Q := ∑ i ∈ Finset.range p, B ^ i with hQ
  have hQB : Q * (B - 1) = B ^ p - 1 := geom_sum_mul B p
  have hcomm : B * Q = Q * B := by
    rw [hQ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (pow_mul_comm' B i).symm
  obtain ⟨u, hu'⟩ : ∃ u, (B - 1) *ᵥ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hB1
    rw [← sub_eq_zero]
    ext i j
    have h := congrFun (hcon (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  set W := LinearMap.ker (Matrix.toLin' Q) with hW
  have hinv : ∀ y ∈ W, Matrix.toLin' B y ∈ W := by
    intro y hy
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy ⊢
    rw [Matrix.toLin'_apply, mulVec_mulVec, ← hcomm, ← mulVec_mulVec, hy, mulVec_zero]
  have hmem : (B - 1) *ᵥ u ∈ W := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, mulVec_mulVec, hQB, hBp, sub_self, zero_mulVec]
  have hne : W ≠ ⊥ := fun h => hu' (by rw [h] at hmem; exact (Submodule.mem_bot L).mp hmem)
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((Matrix.toLin' B).restrict hinv)
  obtain ⟨y, hy⟩ := hμ.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
  have hBy : B *ᵥ (y : ι → L) = μ • (y : ι → L) := by
    have := congrArg Subtype.val hy.1
    simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using this
  have hy0 : (y : ι → L) ≠ 0 := fun h => hy.2 (Subtype.ext h)
  refine ⟨μ, y, hy0, hBy, ?_⟩
  rintro rfl
  have hpow : ∀ k : ℕ, B ^ k *ᵥ (y : ι → L) = (y : ι → L) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBy, one_smul, ih]
  have hQy : Q *ᵥ (y : ι → L) = (p : L) • (y : ι → L) := by
    rw [hQ, Matrix.sum_mulVec]
    simp only [hpow, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul L]
  have hy' := y.2
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, hQy] at hy'
  exact hy0 ((smul_eq_zero.mp hy').resolve_left hp)

theorem eigenvalue_pow_eq_one {B : Matrix ι ι L} {p : ℕ} (hBp : B ^ p = 1) {μ : L}
    {v : ι → L} (hv : v ≠ 0) (hBv : B *ᵥ v = μ • v) : μ ^ p = 1 := by
  have hpow : ∀ k : ℕ, B ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBv, mulVec_smul, ih, smul_smul, pow_succ']
  have h := hpow p
  rw [hBp, one_mulVec] at h
  by_contra hne
  apply hv
  have h' : (μ ^ p - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
  exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)

theorem eigen_map_aux (f : L →+* L) {B : Matrix ι ι L} {μ : L} {v : ι → L} (hv : v ≠ 0)
    (hBv : B *ᵥ v = μ • v) : (f ∘ v) ≠ 0 ∧ B.map f *ᵥ (f ∘ v) = f μ • (f ∘ v) := by
  refine ⟨?_, ?_⟩
  · intro h0
    apply hv
    funext i
    have h := congrFun h0 i
    simp only [Function.comp_apply, Pi.zero_apply] at h
    exact f.injective (h.trans (map_zero f).symm)
  · funext i
    have h : f ((B *ᵥ v) i) = (B.map f *ᵥ (f ∘ v)) i := RingHom.map_mulVec f B v i
    rw [hBv, Pi.smul_apply, smul_eq_mul, map_mul] at h
    rw [Pi.smul_apply, smul_eq_mul]
    exact h.symm

theorem eigen_map (f : L →+* L) {B : Matrix ι ι L} (hBf : B.map f = B) {μ : L} {v : ι → L}
    (hv : v ≠ 0) (hBv : B *ᵥ v = μ • v) : (f ∘ v) ≠ 0 ∧ B *ᵥ (f ∘ v) = f μ • (f ∘ v) := by
  obtain ⟨h1, h2⟩ := eigen_map_aux f hv hBv
  rw [hBf] at h2
  exact ⟨h1, h2⟩

theorem eigen_twist (f : L →+* L) {A B : Matrix ι ι L} (hA : IsUnit A)
    (hAB : A * B.map f = B * A) {μ : L} {v : ι → L} (hv : v ≠ 0) (hBv : B *ᵥ v = μ • v) :
    ∃ w : ι → L, w ≠ 0 ∧ B *ᵥ w = f μ • w := by
  obtain ⟨h0, h1⟩ := eigen_map_aux f hv hBv
  refine ⟨A *ᵥ (f ∘ v), ?_, ?_⟩
  · intro h
    exact h0 ((Matrix.mulVec_injective_iff_isUnit.mpr hA) (h.trans (mulVec_zero A).symm))
  · rw [mulVec_mulVec, ← hAB, ← mulVec_mulVec, h1, mulVec_smul]

theorem eigen_unitary (f : L →+* L) {B : Matrix ι ι L} (hBu : (B.map f)ᵀ * B = 1) {μ : L}
    {v : ι → L} (hv : v ≠ 0) (hBv : B *ᵥ v = μ • v) :
    ∃ w : ι → L, w ≠ 0 ∧ B *ᵥ w = (f μ)⁻¹ • w := by
  obtain ⟨h0, h1⟩ := eigen_map_aux f hv hBv
  set C := B.map f with hC
  have hdet : (scalar ι (f μ) - C).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp
      ⟨f ∘ v, h0, by rw [sub_mulVec, scalar_mulVec_eq, h1, sub_self]⟩
  have hdetT : (scalar ι (f μ) - Cᵀ).det = 0 := by
    rw [← det_transpose, transpose_sub, transpose_transpose, scalar_apply, diagonal_transpose,
      ← scalar_apply]
    exact hdet
  obtain ⟨w, hw, hCw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  rw [sub_mulVec, scalar_mulVec_eq, sub_eq_zero] at hCw
  have hBC : B * Cᵀ = 1 := mul_eq_one_comm.mp hBu
  have hw' : w = f μ • (B *ᵥ w) := by
    calc w = (B * Cᵀ) *ᵥ w := by rw [hBC, one_mulVec]
      _ = f μ • (B *ᵥ w) := by rw [← mulVec_mulVec, ← hCw, mulVec_smul]
  have hfμ : f μ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hw'
    exact hw hw'
  refine ⟨w, hw, ?_⟩
  rw [hw', smul_smul, inv_mul_cancel₀ hfμ, one_smul, ← hw']

theorem card_le_of_eigen {κ : Type*} [Fintype κ] {B : Matrix ι ι L} (lam : κ → L)
    (hlam : Function.Injective lam) (vec : κ → ι → L)
    (hvec : ∀ k, vec k ≠ 0 ∧ B *ᵥ vec k = lam k • vec k) : Fintype.card κ ≤ Fintype.card ι := by
  have hli : LinearIndependent L vec :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B) lam hlam vec fun k => by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact ⟨(hvec k).2, (hvec k).1⟩
  have h := hli.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card] at h

theorem isPrimitiveRoot_of_eigen {B : Matrix ι ι L} {p : ℕ} [Fact p.Prime] (hBp : B ^ p = 1)
    {μ : L} {v : ι → L} (hv : v ≠ 0) (hBv : B *ᵥ v = μ • v) (hμ1 : μ ≠ 1) :
    IsPrimitiveRoot μ p := by
  have hμo : orderOf μ = p := orderOf_eq_prime (eigenvalue_pow_eq_one hBp hv hBv) hμ1
  exact hμo ▸ IsPrimitiveRoot.orderOf μ

end Eig

section Unitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_frob_64_8 [CharP L 2] :
    ∃ f64 f8 : L →+* L, (∀ x, f64 x = x ^ 64) ∧ ∀ x, f8 x = x ^ 8 :=
  ⟨iterateFrobenius L 2 6, iterateFrobenius L 2 3, fun _ => rfl, fun _ => rfl⟩

theorem natCast_ne_zero_of_odd [CharP L 2] {n : ℕ} (hn : n % 2 = 1) : (n : L) ≠ 0 := by
  intro h
  have h' := (CharP.cast_eq_zero_iff L 2 n).mp h
  omega

theorem four_le_card_of_pow_five [CharP L 2] [IsAlgClosed L] {B : Matrix ι ι L}
    (hB64 : B.map (fun x => x ^ 64) = B) (hBu : (B.map (fun x => x ^ 8))ᵀ * B = 1)
    (h5 : B ^ 5 = 1) (hB1 : B ≠ 1) : 4 ≤ Fintype.card ι := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨f64, f8, hf64, hf8⟩ := exists_frob_64_8 (L := L)
  have hB64' : B.map f64 = B := by
    have e : B.map f64 = B.map (fun x => x ^ 64) := by
      ext i j
      simp [hf64]
    rw [e, hB64]
  have hBu' : (B.map f8)ᵀ * B = 1 := by
    have e : B.map f8 = B.map (fun x => x ^ 8) := by
      ext i j
      simp [hf8]
    rw [e, hBu]
  obtain ⟨μ, v, hv, hBv, hμ1⟩ :=
    exists_eigenvalue_ne_one_of_pow_eq_one (natCast_ne_zero_of_odd (L := L) (n := 5) rfl) h5 hB1
  have hμ5 : μ ^ 5 = 1 := eigenvalue_pow_eq_one h5 hv hBv
  have hprim : IsPrimitiveRoot μ 5 := isPrimitiveRoot_of_eigen h5 hv hBv hμ1
  obtain ⟨hv4, hBv4⟩ := eigen_map f64 hB64' hv hBv
  obtain ⟨w2, hw2, hBw2⟩ := eigen_unitary f8 hBu' hv hBv
  obtain ⟨hv3, hBv3⟩ := eigen_map f64 hB64' hw2 hBw2
  have e4 : f64 μ = μ ^ 4 := by
    rw [hf64, show 64 = 5 * 12 + 4 by norm_num, pow_add, pow_mul, hμ5, one_pow, one_mul]
  have e2 : (f8 μ)⁻¹ = μ ^ 2 := by
    rw [hf8]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show 8 + 2 = 5 * 2 by norm_num, pow_mul, hμ5, one_pow]
  have e3 : f64 ((f8 μ)⁻¹) = μ ^ 3 := by
    rw [e2, hf64, ← pow_mul, show 2 * 64 = 5 * 25 + 3 by norm_num, pow_add, pow_mul, hμ5, one_pow,
      one_mul]
  rw [e4] at hBv4
  rw [e3] at hBv3
  rw [e2] at hBw2
  set ex : Fin 4 → ℕ := ![1, 2, 3, 4] with hex
  set lam : Fin 4 → L := fun i => μ ^ ex i with hlam
  set vec : Fin 4 → (ι → L) := ![v, w2, f64 ∘ w2, f64 ∘ v] with hvec
  have hexlt : ∀ i, ex i < 5 := by decide
  have hexinj : ∀ i j, ex i = ex j → i = j := by decide
  have hlaminj : Function.Injective lam := fun i j h =>
    hexinj i j (hprim.pow_inj (hexlt i) (hexlt j) h)
  have hvB : ∀ i, vec i ≠ 0 ∧ B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · exact ⟨by simpa [hvec] using hv, by simpa [hvec, hlam, hex] using hBv⟩
    · exact ⟨by simpa [hvec] using hw2, by simpa [hvec, hlam, hex] using hBw2⟩
    · exact ⟨by simpa [hvec] using hv3, by simpa [hvec, hlam, hex] using hBv3⟩
    · exact ⟨by simpa [hvec] using hv4, by simpa [hvec, hlam, hex] using hBv4⟩
  simpa using card_le_of_eigen lam hlaminj vec hvB

theorem three_le_card_of_pow_nineteen [CharP L 2] [IsAlgClosed L] {B : Matrix ι ι L}
    (hB64 : B.map (fun x => x ^ 64) = B) (hBu : (B.map (fun x => x ^ 8))ᵀ * B = 1)
    (h19 : B ^ 19 = 1) (hB1 : B ≠ 1) : 3 ≤ Fintype.card ι := by
  have : Fact (Nat.Prime 19) := ⟨by decide⟩
  obtain ⟨f64, f8, hf64, hf8⟩ := exists_frob_64_8 (L := L)
  have hB64' : B.map f64 = B := by
    have e : B.map f64 = B.map (fun x => x ^ 64) := by
      ext i j
      simp [hf64]
    rw [e, hB64]
  have hBu' : (B.map f8)ᵀ * B = 1 := by
    have e : B.map f8 = B.map (fun x => x ^ 8) := by
      ext i j
      simp [hf8]
    rw [e, hBu]
  obtain ⟨μ, v, hv, hBv, hμ1⟩ :=
    exists_eigenvalue_ne_one_of_pow_eq_one (natCast_ne_zero_of_odd (L := L) (n := 19) rfl) h19
      hB1
  have hμ19 : μ ^ 19 = 1 := eigenvalue_pow_eq_one h19 hv hBv
  have hprim : IsPrimitiveRoot μ 19 := isPrimitiveRoot_of_eigen h19 hv hBv hμ1
  obtain ⟨hv7, hBv7⟩ := eigen_map f64 hB64' hv hBv
  obtain ⟨w11, hw11, hBw11⟩ := eigen_unitary f8 hBu' hv hBv
  have e7 : f64 μ = μ ^ 7 := by
    rw [hf64, show 64 = 19 * 3 + 7 by norm_num, pow_add, pow_mul, hμ19, one_pow, one_mul]
  have e11 : (f8 μ)⁻¹ = μ ^ 11 := by
    rw [hf8]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show 8 + 11 = 19 by norm_num, hμ19]
  rw [e7] at hBv7
  rw [e11] at hBw11
  set ex : Fin 3 → ℕ := ![1, 7, 11] with hex
  set lam : Fin 3 → L := fun i => μ ^ ex i with hlam
  set vec : Fin 3 → (ι → L) := ![v, f64 ∘ v, w11] with hvec
  have hexlt : ∀ i, ex i < 19 := by decide
  have hexinj : ∀ i j, ex i = ex j → i = j := by decide
  have hlaminj : Function.Injective lam := fun i j h =>
    hexinj i j (hprim.pow_inj (hexlt i) (hexlt j) h)
  have hvB : ∀ i, vec i ≠ 0 ∧ B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · exact ⟨by simpa [hvec] using hv, by simpa [hvec, hlam, hex] using hBv⟩
    · exact ⟨by simpa [hvec] using hv7, by simpa [hvec, hlam, hex] using hBv7⟩
    · exact ⟨by simpa [hvec] using hw11, by simpa [hvec, hlam, hex] using hBw11⟩
  simpa using card_le_of_eigen lam hlaminj vec hvB

theorem six_le_card_of_twisted_pow_seven [CharP L 2] [IsAlgClosed L] {A B : Matrix ι ι L}
    (f : L →+* L) (hf : (∀ x, f x = x ^ 4) ∨ ∀ x, f x = x ^ 16) (hA : IsUnit A)
    (hAB : A * B.map f = B * A) (hBu : (B.map (fun x => x ^ 8))ᵀ * B = 1)
    (h7 : B ^ 7 = 1) (hB1 : B ≠ 1) : 6 ≤ Fintype.card ι := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨-, f8, -, hf8⟩ := exists_frob_64_8 (L := L)
  have hBu' : (B.map f8)ᵀ * B = 1 := by
    have e : B.map f8 = B.map (fun x => x ^ 8) := by
      ext i j
      simp [hf8]
    rw [e, hBu]
  obtain ⟨μ, v, hv, hBv, hμ1⟩ :=
    exists_eigenvalue_ne_one_of_pow_eq_one (natCast_ne_zero_of_odd (L := L) (n := 7) rfl) h7 hB1
  have hμ7 : μ ^ 7 = 1 := eigenvalue_pow_eq_one h7 hv hBv
  have hprim : IsPrimitiveRoot μ 7 := isPrimitiveRoot_of_eigen h7 hv hBv hμ1
  obtain ⟨wa, hwa, hBwa⟩ := eigen_twist f hA hAB hv hBv
  obtain ⟨wb, hwb, hBwb⟩ := eigen_twist f hA hAB hwa hBwa
  obtain ⟨x2, hx2, hBx2, x4, hx4, hBx4⟩ : ∃ x2 : ι → L, x2 ≠ 0 ∧ B *ᵥ x2 = μ ^ 2 • x2 ∧
      ∃ x4 : ι → L, x4 ≠ 0 ∧ B *ᵥ x4 = μ ^ 4 • x4 := by
    rcases hf with hf | hf
    · have e1 : f μ = μ ^ 4 := hf μ
      have e2 : f (f μ) = μ ^ 2 := by
        rw [hf, hf, ← pow_mul, show 4 * 4 = 7 * 2 + 2 by norm_num, pow_add, pow_mul, hμ7, one_pow,
          one_mul]
      rw [e2] at hBwb
      rw [e1] at hBwa
      exact ⟨wb, hwb, hBwb, wa, hwa, hBwa⟩
    · have e1 : f μ = μ ^ 2 := by
        rw [hf, show 16 = 7 * 2 + 2 by norm_num, pow_add, pow_mul, hμ7, one_pow, one_mul]
      have e2 : f (f μ) = μ ^ 4 := by
        rw [hf, hf, ← pow_mul, show 16 * 16 = 7 * 36 + 4 by norm_num, pow_add, pow_mul, hμ7,
          one_pow, one_mul]
      rw [e2] at hBwb
      rw [e1] at hBwa
      exact ⟨wa, hwa, hBwa, wb, hwb, hBwb⟩
  obtain ⟨y6, hy6, hBy6⟩ := eigen_unitary f8 hBu' hv hBv
  obtain ⟨y5, hy5, hBy5⟩ := eigen_unitary f8 hBu' hx2 hBx2
  obtain ⟨y3, hy3, hBy3⟩ := eigen_unitary f8 hBu' hx4 hBx4
  have e6 : (f8 μ)⁻¹ = μ ^ 6 := by
    rw [hf8]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show 8 + 6 = 7 * 2 by norm_num, pow_mul, hμ7, one_pow]
  have e5 : (f8 (μ ^ 2))⁻¹ = μ ^ 5 := by
    rw [hf8]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_mul, ← pow_add, show 2 * 8 + 5 = 7 * 3 by norm_num, pow_mul, hμ7, one_pow]
  have e3 : (f8 (μ ^ 4))⁻¹ = μ ^ 3 := by
    rw [hf8]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_mul, ← pow_add, show 4 * 8 + 3 = 7 * 5 by norm_num, pow_mul, hμ7, one_pow]
  rw [e6] at hBy6
  rw [e5] at hBy5
  rw [e3] at hBy3
  set ex : Fin 6 → ℕ := ![1, 2, 3, 4, 5, 6] with hex
  set lam : Fin 6 → L := fun i => μ ^ ex i with hlam
  set vec : Fin 6 → (ι → L) := ![v, x2, y3, x4, y5, y6] with hvec
  have hexlt : ∀ i, ex i < 7 := by decide
  have hexinj : ∀ i j, ex i = ex j → i = j := by decide
  have hlaminj : Function.Injective lam := fun i j h =>
    hexinj i j (hprim.pow_inj (hexlt i) (hexlt j) h)
  have hvB : ∀ i, vec i ≠ 0 ∧ B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · exact ⟨by simpa [hvec] using hv, by simpa [hvec, hlam, hex] using hBv⟩
    · exact ⟨by simpa [hvec] using hx2, by simpa [hvec, hlam, hex] using hBx2⟩
    · exact ⟨by simpa [hvec] using hy3, by simpa [hvec, hlam, hex] using hBy3⟩
    · exact ⟨by simpa [hvec] using hx4, by simpa [hvec, hlam, hex] using hBx4⟩
    · exact ⟨by simpa [hvec] using hy5, by simpa [hvec, hlam, hex] using hBy5⟩
    · exact ⟨by simpa [hvec] using hy6, by simpa [hvec, hlam, hex] using hBy6⟩
  simpa using card_le_of_eigen lam hlaminj vec hvB

theorem eq_one_of_commute_of_pow_five [CharP L 2] [IsAlgClosed L]
    {B U : Matrix (Fin 5) (Fin 5) L} (hB64 : B.map (fun x => x ^ 64) = B)
    (hBu : (B.map (fun x => x ^ 8))ᵀ * B = 1) (hdet : B.det = 1) (h5 : B ^ 5 = 1) (hB1 : B ≠ 1)
    (hU2 : U ^ 2 = 1) (hUB : U * B = B * U) : U = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨f64, f8, hf64, hf8⟩ := exists_frob_64_8 (L := L)
  have hB64' : B.map f64 = B := by
    have e : B.map f64 = B.map (fun x => x ^ 64) := by
      ext i j
      simp [hf64]
    rw [e, hB64]
  have hBu' : (B.map f8)ᵀ * B = 1 := by
    have e : B.map f8 = B.map (fun x => x ^ 8) := by
      ext i j
      simp [hf8]
    rw [e, hBu]
  obtain ⟨μ, v, hv, hBv, hμ1⟩ :=
    exists_eigenvalue_ne_one_of_pow_eq_one (natCast_ne_zero_of_odd (L := L) (n := 5) rfl) h5 hB1
  have hμ5 : μ ^ 5 = 1 := eigenvalue_pow_eq_one h5 hv hBv
  have hprim : IsPrimitiveRoot μ 5 := isPrimitiveRoot_of_eigen h5 hv hBv hμ1
  obtain ⟨hv4, hBv4⟩ := eigen_map f64 hB64' hv hBv
  obtain ⟨w2, hw2, hBw2⟩ := eigen_unitary f8 hBu' hv hBv
  obtain ⟨hv3, hBv3⟩ := eigen_map f64 hB64' hw2 hBw2
  have e4 : f64 μ = μ ^ 4 := by
    rw [hf64, show 64 = 5 * 12 + 4 by norm_num, pow_add, pow_mul, hμ5, one_pow, one_mul]
  have e2 : (f8 μ)⁻¹ = μ ^ 2 := by
    rw [hf8]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show 8 + 2 = 5 * 2 by norm_num, pow_mul, hμ5, one_pow]
  have e3 : f64 ((f8 μ)⁻¹) = μ ^ 3 := by
    rw [e2, hf64, ← pow_mul, show 2 * 64 = 5 * 25 + 3 by norm_num, pow_add, pow_mul, hμ5, one_pow,
      one_mul]
  rw [e4] at hBv4
  rw [e3] at hBv3
  rw [e2] at hBw2
  have hmon := B.charpoly_monic
  have hroot : ∀ c : L, ∀ w : Fin 5 → L, w ≠ 0 → B *ᵥ w = c • w → c ∈ B.charpoly.roots := by
    intro c w hw hBw
    rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly]
    exact Matrix.exists_mulVec_eq_zero_iff.mp
      ⟨w, hw, by rw [sub_mulVec, scalar_mulVec_eq, hBw, sub_self]⟩
  have hne : ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → μ ^ i ≠ μ ^ j := fun i j hi hj hij h =>
    hij (hprim.pow_inj hi hj h)
  set M4 : Multiset L := μ ::ₘ (μ ^ 2) ::ₘ (μ ^ 3) ::ₘ {μ ^ 4} with hM4
  have hM4nd : M4.Nodup := by
    have h12 := hne 1 2 (by norm_num) (by norm_num) (by norm_num)
    have h13 := hne 1 3 (by norm_num) (by norm_num) (by norm_num)
    have h14 := hne 1 4 (by norm_num) (by norm_num) (by norm_num)
    have h23 := hne 2 3 (by norm_num) (by norm_num) (by norm_num)
    have h24 := hne 2 4 (by norm_num) (by norm_num) (by norm_num)
    have h34 := hne 3 4 (by norm_num) (by norm_num) (by norm_num)
    rw [pow_one] at h12 h13 h14
    simp [hM4, h12, h13, h14, h23, h24, h34]
  have hM4le : M4 ≤ B.charpoly.roots := by
    rw [Multiset.le_iff_subset hM4nd]
    intro x hx
    simp only [hM4, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hroot _ v hv hBv
    · exact hroot _ w2 hw2 hBw2
    · exact hroot _ _ hv3 hBv3
    · exact hroot _ _ hv4 hBv4
  obtain ⟨R', hR'⟩ := Multiset.le_iff_exists_add.mp hM4le
  have hcard : Multiset.card B.charpoly.roots = 5 := by
    rw [(Polynomial.splits_iff_card_roots).mp (IsAlgClosed.splits _),
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hR'card : Multiset.card R' = 1 := by
    have h := congrArg Multiset.card hR'
    rw [Multiset.card_add, hcard] at h
    simp [hM4] at h
    omega
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp hR'card
  have hprod : B.det = μ ^ 10 * c := by
    rw [Matrix.det_eq_prod_roots_charpoly, hR', hc]
    simp only [hM4, Multiset.prod_add, Multiset.prod_cons, Multiset.prod_singleton]
    ring
  have hμ10 : μ ^ 10 = 1 := by rw [show 10 = 5 * 2 by norm_num, pow_mul, hμ5, one_pow]
  have hc1 : c = 1 := by
    rw [hdet, hμ10, one_mul] at hprod
    exact hprod.symm
  have h1mem : (1 : L) ∈ B.charpoly.roots := by
    rw [hR', hc, hc1]
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self 1))
  obtain ⟨v0, hv0, hBv0⟩ : ∃ w : Fin 5 → L, w ≠ 0 ∧ B *ᵥ w = μ ^ 0 • w := by
    rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot, Matrix.eval_charpoly] at h1mem
    obtain ⟨w, hw, hBw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1mem
    refine ⟨w, hw, ?_⟩
    rw [sub_mulVec, scalar_mulVec_eq, sub_eq_zero] at hBw
    rw [pow_zero]
    exact hBw.symm
  set lam : Fin 5 → L := fun i => μ ^ (i : ℕ) with hlam
  set vec : Fin 5 → (Fin 5 → L) := ![v0, v, w2, f64 ∘ w2, f64 ∘ v] with hvec
  have hlaminj : Function.Injective lam := fun i j h => Fin.ext (hprim.pow_inj i.2 j.2 h)
  have hvB : ∀ i, vec i ≠ 0 ∧ B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · exact ⟨by simpa [hvec] using hv0, by simpa [hvec, hlam] using hBv0⟩
    · exact ⟨by simpa [hvec] using hv, by simpa [hvec, hlam] using hBv⟩
    · exact ⟨by simpa [hvec] using hw2, by simpa [hvec, hlam] using hBw2⟩
    · exact ⟨by simpa [hvec] using hv3, by simpa [hvec, hlam] using hBv3⟩
    · exact ⟨by simpa [hvec] using hv4, by simpa [hvec, hlam] using hBv4⟩
  have hli : LinearIndependent L vec :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B) lam hlaminj vec fun k => by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact ⟨(hvB k).2, (hvB k).1⟩
  have hspan : Submodule.span L (Set.range vec) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hU : ∀ i, U *ᵥ vec i = vec i := by
    intro i
    have hmem : U *ᵥ vec i ∈ Submodule.span L (Set.range vec) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hmem
    have hBU : B *ᵥ (U *ᵥ vec i) = lam i • (U *ᵥ vec i) := by
      rw [mulVec_mulVec, ← hUB, ← mulVec_mulVec, (hvB i).2, mulVec_smul]
    have hsum : ∑ j, (c j * (lam j - lam i)) • vec j = 0 := by
      have h0 : B *ᵥ (∑ j, c j • vec j) - lam i • (∑ j, c j • vec j) = 0 := by
        rw [hc, hBU, sub_self]
      rw [← h0, mulVec_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mulVec_smul, (hvB j).2, smul_smul, smul_smul, ← sub_smul, mul_sub, mul_comm (lam i)]
    have hcoef := Fintype.linearIndependent_iff.mp hli _ hsum
    have hcj : ∀ j, j ≠ i → c j = 0 := fun j hji =>
      (mul_eq_zero.mp (hcoef j)).resolve_right (sub_ne_zero.mpr fun h => hji (hlaminj h))
    have hUv : U *ᵥ vec i = c i • vec i := by
      rw [← hc, Finset.sum_eq_single i (fun j _ hji => by rw [hcj j hji, zero_smul])
        (fun h => absurd (Finset.mem_univ i) h)]
    have hc2 : c i ^ 2 = 1 := by
      have h := congrArg (fun w => U *ᵥ w) hUv
      rw [mulVec_mulVec, ← pow_two, hU2, one_mulVec, mulVec_smul, hUv, smul_smul] at h
      have h' : (c i * c i - 1) • vec i = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
      have := (smul_eq_zero.mp h').resolve_right (hvB i).1
      linear_combination this
    have hci : c i = 1 := by
      have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
      have h : (c i - 1) ^ 2 = 0 := by linear_combination hc2 - (c i - 1) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
    rw [hUv, hci, one_smul]
  have hlin : Matrix.toLin' U = Matrix.toLin' (1 : Matrix (Fin 5) (Fin 5) L) :=
    LinearMap.ext_on_range hspan fun i => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, one_mulVec, hU i]
  exact Matrix.toLin'.injective hlin

end Unitary

section Finite

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem pow_sixtyfour_of_card (hF : Nat.card F = 64) (x : F) : x ^ 64 = x := by
  letI := Fintype.ofFinite F
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hF] at h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem transfer_facts (hF : Nat.card F = 64) {B : Matrix ι ι F}
    (hBu : (B.map (iterateFrobenius F 2 3))ᵀ * B = 1) :
    letI ψ := algebraMap F (AlgebraicClosure F)
    (B.map ψ).map (fun x => x ^ 64) = B.map ψ ∧
      ((B.map ψ).map (fun x => x ^ 8))ᵀ * B.map ψ = 1 := by
  set ψ := algebraMap F (AlgebraicClosure F) with hψ
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.map_apply]
    rw [← map_pow, pow_sixtyfour_of_card hF]
  · have h8 : (B.map ψ).map (fun x => x ^ 8) = (B.map (iterateFrobenius F 2 3)).map ψ := by
      ext i j
      simp only [Matrix.map_apply]
      rw [← map_pow]
      rfl
    rw [h8, ← transpose_map, ← Matrix.map_mul, hBu, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]

theorem eq_one_of_pow_five_of_card_lt (hF : Nat.card F = 64) {B : Matrix ι ι F}
    (hBu : (B.map (iterateFrobenius F 2 3))ᵀ * B = 1) (h5 : B ^ 5 = 1)
    (hcard : Fintype.card ι < 4) : B = 1 := by
  by_contra hB1
  set ψ := algebraMap F (AlgebraicClosure F) with hψ
  have : CharP (AlgebraicClosure F) 2 := charP_of_injective_algebraMap ψ.injective 2
  have hinj : Function.Injective (ψ.mapMatrix (m := ι)) :=
    Matrix.map_injective ψ.injective
  obtain ⟨h64, hu⟩ := transfer_facts hF hBu
  have h := four_le_card_of_pow_five (B := B.map ψ) h64 hu
    (by rw [← RingHom.mapMatrix_apply, ← map_pow, h5, map_one])
    (fun h => hB1 (hinj (by rw [RingHom.mapMatrix_apply, h, map_one])))
  omega

theorem eq_one_of_pow_nineteen_of_card_lt (hF : Nat.card F = 64) {B : Matrix ι ι F}
    (hBu : (B.map (iterateFrobenius F 2 3))ᵀ * B = 1) (h19 : B ^ 19 = 1)
    (hcard : Fintype.card ι < 3) : B = 1 := by
  by_contra hB1
  set ψ := algebraMap F (AlgebraicClosure F) with hψ
  have : CharP (AlgebraicClosure F) 2 := charP_of_injective_algebraMap ψ.injective 2
  have hinj : Function.Injective (ψ.mapMatrix (m := ι)) :=
    Matrix.map_injective ψ.injective
  obtain ⟨h64, hu⟩ := transfer_facts hF hBu
  have h := three_le_card_of_pow_nineteen (B := B.map ψ) h64 hu
    (by rw [← RingHom.mapMatrix_apply, ← map_pow, h19, map_one])
    (fun h => hB1 (hinj (by rw [RingHom.mapMatrix_apply, h, map_one])))
  omega

theorem eq_one_of_commute_of_pow_five' (hF : Nat.card F = 64) {B U : Matrix (Fin 5) (Fin 5) F}
    (hBu : (B.map (iterateFrobenius F 2 3))ᵀ * B = 1) (hdet : B.det = 1) (h5 : B ^ 5 = 1)
    (hB1 : B ≠ 1) (hU2 : U ^ 2 = 1) (hUB : U * B = B * U) : U = 1 := by
  set ψ := algebraMap F (AlgebraicClosure F) with hψ
  have : CharP (AlgebraicClosure F) 2 := charP_of_injective_algebraMap ψ.injective 2
  have hinj : Function.Injective (ψ.mapMatrix (m := Fin 5)) :=
    Matrix.map_injective ψ.injective
  obtain ⟨h64, hu⟩ := transfer_facts hF hBu
  apply hinj
  rw [map_one]
  exact eq_one_of_commute_of_pow_five (B := B.map ψ) h64 hu
    (by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one])
    (by rw [← RingHom.mapMatrix_apply, ← map_pow, h5, map_one])
    (fun h => hB1 (hinj (by rw [RingHom.mapMatrix_apply, h, map_one])))
    (by rw [RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_pow, hU2, map_one])
    (by rw [RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
      ← map_mul, ← map_mul, hUB])

theorem eq_one_of_twisted_pow_seven' (hF : Nat.card F = 64) {A B : Matrix (Fin 5) (Fin 5) F}
    (φ : F →+* F) (hφ : (∀ x, φ x = x ^ 4) ∨ ∀ x, φ x = x ^ 16) (hA : IsUnit A)
    (hAB : A * B.map φ = B * A) (hBu : (B.map (iterateFrobenius F 2 3))ᵀ * B = 1)
    (h7 : B ^ 7 = 1) : B = 1 := by
  by_contra hB1
  set ψ := algebraMap F (AlgebraicClosure F) with hψ
  have : CharP (AlgebraicClosure F) 2 := charP_of_injective_algebraMap ψ.injective 2
  have hinj : Function.Injective (ψ.mapMatrix (m := Fin 5)) :=
    Matrix.map_injective ψ.injective
  obtain ⟨-, hu⟩ := transfer_facts hF hBu
  obtain ⟨f, hf, hfφ⟩ : ∃ f : AlgebraicClosure F →+* AlgebraicClosure F,
      ((∀ x, f x = x ^ 4) ∨ ∀ x, f x = x ^ 16) ∧ ∀ x : F, f (ψ x) = ψ (φ x) := by
    rcases hφ with hφ | hφ
    · exact ⟨iterateFrobenius _ 2 2, Or.inl fun _ => rfl, fun x => by
        rw [hφ, map_pow]
        rfl⟩
    · exact ⟨iterateFrobenius _ 2 4, Or.inr fun _ => rfl, fun x => by
        rw [hφ, map_pow]
        rfl⟩
  have hmapφ : (B.map ψ).map f = (B.map φ).map ψ := by
    ext i j
    simp only [Matrix.map_apply]
    exact hfφ _
  have h := six_le_card_of_twisted_pow_seven (A := A.map ψ) (B := B.map ψ) f hf
    (by
      rw [← RingHom.mapMatrix_apply]
      exact hA.map _)
    (by
      rw [hmapφ, ← Matrix.map_mul, ← Matrix.map_mul, hAB])
    hu (by rw [← RingHom.mapMatrix_apply, ← map_pow, h7, map_one])
    (fun h => hB1 (hinj (by rw [RingHom.mapMatrix_apply, h, map_one])))
  simp at h

end Finite

end CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV
