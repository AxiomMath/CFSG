module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVSp64Lin
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open Matrix CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV

variable {L : Type*} [Field L]

theorem exists_eigenvalue_ne_one_of_pow [IsAlgClosed L] {p : ℕ} (hpne : (p : L) ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι L} (hp : B ^ p = 1) (hB1 : B ≠ 1) :
    ∃ μ : L, ∃ v : ι → L, v ≠ 0 ∧ B *ᵥ v = μ • v ∧ μ ≠ 1 := by
  set Q := ∑ k ∈ Finset.range p, B ^ k with hQ
  have hQB : Q * (B - 1) = B ^ p - 1 := by rw [hQ, geom_sum_mul]
  have hcomm : B * Q = Q * B := by
    rw [hQ, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_succ', ← pow_succ]
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
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, mulVec_mulVec, hQB, hp, sub_self, zero_mulVec]
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
    simp only [hpow, Finset.sum_const, Finset.card_range]
    rw [Nat.cast_smul_eq_nsmul]
  have hy' := y.2
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, hQy] at hy'
  exact hy0 ((smul_eq_zero.mp hy').resolve_left hpne)

theorem sp_trivial_of_commute_pow_thirteen [IsAlgClosed L] [CharP L 2]
    {B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L} {b : Fin 3 → Lˣ}
    (hB4 : B.map (fun x => x ^ 4) = B) (h13 : B ^ 13 = 1) (hB1 : B ≠ 1)
    (hb : ∀ i, b i ^ 3 = 1)
    (hAB : diagonal (Sum.elim (fun i => (b i : L)) fun i => ((b i)⁻¹ : Lˣ)) * B =
      B * diagonal (Sum.elim (fun i => (b i : L)) fun i => ((b i)⁻¹ : Lˣ))) :
    ∀ i, b i = 1 := by
  classical
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  set y : Fin 3 ⊕ Fin 3 → L := Sum.elim (fun i => (b i : L)) fun i => ((b i)⁻¹ : Lˣ) with hy
  set A := diagonal y with hA
  have hy3 : ∀ k, y k ^ 3 = 1 := by
    rintro (i | i)
    · simp only [hy, Sum.elim_inl]
      rw [← Units.val_pow_eq_pow_val, hb i, Units.val_one]
    · simp only [hy, Sum.elim_inr]
      rw [← Units.val_pow_eq_pow_val, inv_pow, hb i, inv_one, Units.val_one]
  obtain ⟨φ, hφ⟩ : ∃ φ : L →+* L, ∀ x : L, φ x = x ^ 4 :=
    ⟨iterateFrobenius L 2 2, fun x => rfl⟩
  have hBφ : B.map φ = B := by
    have h4 : B.map φ = B.map (fun x => x ^ 4) := by
      ext i j
      simp [hφ]
    rw [h4, hB4]
  have hAφ : A.map φ = A := by
    ext k l
    simp only [hA, Matrix.map_apply, diagonal_apply]
    split_ifs
    · rw [hφ, pow_succ, hy3, one_mul]
    · exact map_zero φ
  have h13ne : ((13 : ℕ) : L) ≠ 0 := by
    intro h'
    rw [CharP.cast_eq_zero_iff L 2] at h'
    norm_num at h'
  obtain ⟨μ, v, hv, hBv, hμ1⟩ := exists_eigenvalue_ne_one_of_pow h13ne h13 hB1
  have hpowv : ∀ k : ℕ, B ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBv, mulVec_smul, ih, smul_smul, pow_succ']
  have hμ13 : μ ^ 13 = 1 := by
    have h := hpowv 13
    rw [h13, one_mulVec] at h
    by_contra hne
    apply hv
    have h' : (μ ^ 13 - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  have hμo : orderOf μ = 13 := orderOf_eq_prime hμ13 hμ1
  have hprim : IsPrimitiveRoot μ 13 := hμo ▸ IsPrimitiveRoot.orderOf μ
  have hAB' : A * B = B * A := hAB
  obtain ⟨c, w, hw, hBw, hAw⟩ := exists_common_eigenvector hAB' hv hBv
  have hc3 : c ^ 3 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw (funext hcon)
    have hyk : y k = c := by
      by_contra hne
      exact hk (apply_eq_zero_of_diagonal_mulVec hAw hne)
    rw [← hyk]
    exact hy3 k
  have hφc : φ c = c := by rw [hφ, pow_succ, hc3, one_mul]
  obtain ⟨hw₁, hBw₁, hAw₁⟩ := frobenius_eigenvector φ hBφ hAφ hw hBw hAw
  rw [hφc] at hAw₁
  obtain ⟨hw₂, hBw₂, hAw₂⟩ := frobenius_eigenvector φ hBφ hAφ hw₁ hBw₁ hAw₁
  rw [hφc] at hAw₂
  obtain ⟨hw₃, hBw₃, hAw₃⟩ := frobenius_eigenvector φ hBφ hAφ hw₂ hBw₂ hAw₂
  rw [hφc] at hAw₃
  obtain ⟨hw₄, hBw₄, hAw₄⟩ := frobenius_eigenvector φ hBφ hAφ hw₃ hBw₃ hAw₃
  rw [hφc] at hAw₄
  obtain ⟨hw₅, hBw₅, hAw₅⟩ := frobenius_eigenvector φ hBφ hAφ hw₄ hBw₄ hAw₄
  rw [hφc] at hAw₅
  have hred : ∀ a b : ℕ, a = 13 * (a / 13) + b → μ ^ a = μ ^ b := by
    intro a b h
    rw [h, pow_add, pow_mul, hμ13, one_pow, one_mul]
  have e1 : φ μ = μ ^ 4 := hφ μ
  have e2 : φ (φ μ) = μ ^ 3 := by
    rw [e1, hφ, ← pow_mul]
    exact hred 16 3 (by norm_num)
  have e3 : φ (φ (φ μ)) = μ ^ 12 := by
    rw [e2, hφ, ← pow_mul]
  have e4 : φ (φ (φ (φ μ))) = μ ^ 9 := by
    rw [e3, hφ, ← pow_mul]
    exact hred 48 9 (by norm_num)
  have e5 : φ (φ (φ (φ (φ μ)))) = μ ^ 10 := by
    rw [e4, hφ, ← pow_mul]
    exact hred 36 10 (by norm_num)
  rw [e1] at hBw₁
  rw [e2] at hBw₂
  rw [e3] at hBw₃
  rw [e4] at hBw₄
  rw [e5] at hBw₅
  set ex : Fin 6 → ℕ := ![1, 4, 3, 12, 9, 10] with hex
  set lam : Fin 6 → L := fun i => μ ^ ex i with hlam
  set vec : Fin 6 → (Fin 3 ⊕ Fin 3 → L) :=
    ![w, φ ∘ w, φ ∘ (φ ∘ w), φ ∘ (φ ∘ (φ ∘ w)), φ ∘ (φ ∘ (φ ∘ (φ ∘ w))),
      φ ∘ (φ ∘ (φ ∘ (φ ∘ (φ ∘ w))))] with hvec
  have hexlt : ∀ i, ex i < 13 := by decide
  have hexinj : ∀ i j, ex i = ex j → i = j := by decide
  have hlaminj : Function.Injective lam := fun i j h =>
    hexinj i j (hprim.pow_inj (hexlt i) (hexlt j) h)
  have hvecB : ∀ i, B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · simpa [hvec, hlam, hex] using hBw
    · simpa [hvec, hlam, hex] using hBw₁
    · simpa [hvec, hlam, hex] using hBw₂
    · simpa [hvec, hlam, hex] using hBw₃
    · simpa [hvec, hlam, hex] using hBw₄
    · simpa [hvec, hlam, hex] using hBw₅
  have hvec0 : ∀ i, vec i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hvec] using hw
    · simpa [hvec] using hw₁
    · simpa [hvec] using hw₂
    · simpa [hvec] using hw₃
    · simpa [hvec] using hw₄
    · simpa [hvec] using hw₅
  have hli : LinearIndependent L vec :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B) lam hlaminj vec fun i => by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact ⟨hvecB i, hvec0 i⟩
  set I := Finset.univ.filter (fun k => y k = c) with hI
  have hsuppc : ∀ {x : Fin 3 ⊕ Fin 3 → L}, A *ᵥ x = c • x → ∀ k, k ∉ I → x k = 0 := by
    intro x hx k hk
    refine apply_eq_zero_of_diagonal_mulVec hx ?_
    simpa [hI] using hk
  have hcardU : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by simp
  have h6 : 6 ≤ I.card := by
    have := card_le_of_linearIndependent_supported hli I (by
      intro j k hk
      fin_cases j
      · exact hsuppc hAw k hk
      · exact hsuppc hAw₁ k hk
      · exact hsuppc hAw₂ k hk
      · exact hsuppc hAw₃ k hk
      · exact hsuppc hAw₄ k hk
      · exact hsuppc hAw₅ k hk)
    simpa using this
  have hIu : I = Finset.univ := Finset.eq_univ_of_card I (by
    have := Finset.card_le_univ I
    rw [hcardU] at this ⊢
    omega)
  intro i
  have h1 : y (Sum.inl i) = c := by
    have := Finset.mem_univ (Sum.inl i : Fin 3 ⊕ Fin 3)
    rw [← hIu, hI, Finset.mem_filter] at this
    exact this.2
  have h2 : y (Sum.inr i) = c := by
    have := Finset.mem_univ (Sum.inr i : Fin 3 ⊕ Fin 3)
    rw [← hIu, hI, Finset.mem_filter] at this
    exact this.2
  simp only [hy, Sum.elim_inl, Sum.elim_inr] at h1 h2
  apply Units.ext
  have hmul : (b i : L) * ((b i)⁻¹ : Lˣ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [h1, h2] at hmul
  rw [h1, Units.val_one]
  calc c = c ^ 3 * (c * c)⁻¹ := by
        rw [hmul, inv_one, mul_one, show c ^ 3 = c * c * c by ring, hmul, one_mul]
    _ = 1 := by rw [hc3, hmul, inv_one, one_mul]

theorem sp_trivial_of_commute_pow_thirteen' {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F} {b : Fin 3 → Fˣ}
    (h13 : B ^ 13 = 1) (hB1 : B ≠ 1) (hb : ∀ i, b i ^ 3 = 1)
    (hAB : diagonal (Sum.elim (fun i => (b i : F)) fun i => ((b i)⁻¹ : Fˣ)) * B =
      B * diagonal (Sum.elim (fun i => (b i : F)) fun i => ((b i)⁻¹ : Fˣ))) :
    ∀ i, b i = 1 := by
  have hpow4 : ∀ x : F, x ^ 4 = x := by
    intro x
    letI := Fintype.ofFinite F
    have h := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hF] at h
    exact h
  set L := AlgebraicClosure F
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap F L).injective 2
  set ι := (algebraMap F L).mapMatrix (m := Fin 3 ⊕ Fin 3) with hι
  have hinj : Function.Injective ι := Matrix.map_injective (algebraMap F L).injective
  set b' : Fin 3 → Lˣ := fun i => Units.map (algebraMap F L).toMonoidHom (b i) with hb'
  have hdiag : ι (diagonal (Sum.elim (fun i => (b i : F)) fun i => ((b i)⁻¹ : Fˣ))) =
      diagonal (Sum.elim (fun i => (b' i : L)) fun i => ((b' i)⁻¹ : Lˣ)) := by
    rw [hι, RingHom.mapMatrix_apply, diagonal_map (map_zero _)]
    congr 1
    funext k
    rcases k with k | k <;> simp [hb']
  have hres := sp_trivial_of_commute_pow_thirteen (L := L) (B := ι B) (b := b')
    (by
      ext i j
      simp only [hι, RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [← map_pow, hpow4])
    (by rw [← map_pow, h13, map_one])
    (fun h => hB1 (hinj (by rw [h, map_one])))
    (fun i => by rw [hb', ← map_pow, hb i, map_one])
    (by rw [← hdiag, ← map_mul, ← map_mul, hAB])
  intro i
  apply Units.ext
  apply (algebraMap F L).injective
  have := congrArg Units.val (hres i)
  simpa [hb'] using this

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
