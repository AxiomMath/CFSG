module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV

open Matrix

theorem card_le_of_linearIndependent_supported {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {L : Type*} [Field L] {v : κ → ι → L} (hv : LinearIndependent L v)
    (I : Finset ι) (hsupp : ∀ j k, k ∉ I → v j k = 0) : Fintype.card κ ≤ I.card := by
  let ρ : (ι → L) →ₗ[L] (I → L) :=
    { toFun := fun u k => u k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W : Submodule L (ι → L) :=
    { carrier := {u | ∀ k, k ∉ I → u k = 0}
      add_mem' := fun {a b} ha hb k hk => by simp [ha k hk, hb k hk]
      zero_mem' := fun k _ => rfl
      smul_mem' := fun c u hu k hk => by simp [hu k hk] }
  have hspan : Submodule.span L (Set.range v) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩ k hk
    exact hsupp j k hk
  have hdisj : Disjoint (Submodule.span L (Set.range v)) (LinearMap.ker ρ) := by
    rw [Submodule.disjoint_def]
    intro u hu hker
    have hW := hspan hu
    funext k
    by_cases hk : k ∈ I
    · have := congrFun (LinearMap.mem_ker.mp hker) ⟨k, hk⟩
      simpa [ρ] using this
    · exact hW k hk
  have hli := hv.map hdisj
  have h := hli.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

theorem apply_eq_zero_of_diagonal_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {L : Type*}
    [Field L] {y : ι → L} {γ : L} {u : ι → L} (h : diagonal y *ᵥ u = γ • u) {k : ι}
    (hk : y k ≠ γ) : u k = 0 := by
  have h1 := congrFun h k
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : (y k - γ) * u k = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hk)

variable {L : Type*} [Field L]

theorem exists_common_eigenvector [IsAlgClosed L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι L} (hAB : A * B = B * A) {μ : L} {v : ι → L} (hv : v ≠ 0)
    (hBv : B *ᵥ v = μ • v) :
    ∃ (c : L) (w : ι → L), w ≠ 0 ∧ B *ᵥ w = μ • w ∧ A *ᵥ w = c • w := by
  set E := LinearMap.ker (Matrix.toLin' (B - μ • 1)) with hE
  have hinv : ∀ y ∈ E, Matrix.toLin' A y ∈ E := by
    intro y hy
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy ⊢
    have hc : (B - μ • 1) * A = A * (B - μ • 1) := by
      rw [sub_mul, mul_sub, ← hAB, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
    rw [Matrix.toLin'_apply, mulVec_mulVec, hc, ← mulVec_mulVec, hy, mulVec_zero]
  have hvE : v ∈ E := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, sub_mulVec, hBv, smul_mulVec, one_mulVec,
      sub_self]
  have hne : E ≠ ⊥ := fun h => hv (by rw [h] at hvE; exact (Submodule.mem_bot L).mp hvE)
  have : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((Matrix.toLin' A).restrict hinv)
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
  have hAy : A *ᵥ (y : ι → L) = c • (y : ι → L) := by
    have := congrArg Subtype.val hy.1
    simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using this
  have hy0 : (y : ι → L) ≠ 0 := fun h => hy.2 (Subtype.ext h)
  have hBy : B *ᵥ (y : ι → L) = μ • (y : ι → L) := by
    have h := y.2
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, sub_mulVec, smul_mulVec, one_mulVec,
      sub_eq_zero] at h
    exact h
  exact ⟨c, y, hy0, hBy, hAy⟩

theorem frobenius_eigenvector {ι : Type*} [Fintype ι] {A B : Matrix ι ι L} (φ : L →+* L)
    (hBφ : B.map φ = B) (hAφ : A.map φ = A) {μ c : L} {w : ι → L} (hw : w ≠ 0)
    (hBw : B *ᵥ w = μ • w) (hAw : A *ᵥ w = c • w) :
    (φ ∘ w) ≠ 0 ∧ B *ᵥ (φ ∘ w) = φ μ • (φ ∘ w) ∧ A *ᵥ (φ ∘ w) = φ c • (φ ∘ w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply hw
    funext i
    have h := congrFun h0 i
    simp only [Function.comp_apply, Pi.zero_apply] at h
    exact φ.injective (h.trans (map_zero φ).symm)
  · funext i
    have h : φ ((B *ᵥ w) i) = (B.map φ *ᵥ (φ ∘ w)) i := RingHom.map_mulVec φ B w i
    rw [hBw, hBφ, Pi.smul_apply, smul_eq_mul, map_mul] at h
    rw [Pi.smul_apply, smul_eq_mul]
    exact h.symm
  · funext i
    have h : φ ((A *ᵥ w) i) = (A.map φ *ᵥ (φ ∘ w)) i := RingHom.map_mulVec φ A w i
    rw [hAw, hAφ, Pi.smul_apply, smul_eq_mul, map_mul] at h
    rw [Pi.smul_apply, smul_eq_mul]
    exact h.symm

theorem exists_eigenvalue_ne_one_of_pow_seven [IsAlgClosed L] (h7ne : (7 : L) ≠ 0) {ι : Type*}
    [Fintype ι] [DecidableEq ι] {B : Matrix ι ι L} (h7 : B ^ 7 = 1) (hB1 : B ≠ 1) :
    ∃ μ : L, ∃ v : ι → L, v ≠ 0 ∧ B *ᵥ v = μ • v ∧ μ ≠ 1 := by
  set Q := B ^ 6 + B ^ 5 + B ^ 4 + B ^ 3 + B ^ 2 + B + 1 with hQ
  have hQB : Q * (B - 1) = B ^ 7 - 1 := by rw [hQ]; noncomm_ring
  have hcomm : B * Q = Q * B := by rw [hQ]; noncomm_ring
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
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, mulVec_mulVec, hQB, h7, sub_self, zero_mulVec]
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
  have hQy : Q *ᵥ (y : ι → L) = (7 : L) • (y : ι → L) := by
    have h1 := hpow 1
    rw [pow_one] at h1
    rw [hQ, add_mulVec, add_mulVec, add_mulVec, add_mulVec, add_mulVec, add_mulVec, hpow, hpow,
      hpow, hpow, hpow, h1, one_mulVec, show (7 : L) = 1 + 1 + 1 + 1 + 1 + 1 + 1 by norm_num,
      add_smul, add_smul, add_smul, add_smul, add_smul, add_smul, one_smul]
  have hy' := y.2
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, hQy] at hy'
  exact hy0 ((smul_eq_zero.mp hy').resolve_left h7ne)

theorem sp_trivial_or_regular_of_commute_pow_seven [IsAlgClosed L] [CharP L 2]
    {B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L} {b : Fin 3 → Lˣ}
    (hB4 : B.map (fun x => x ^ 4) = B) (h7 : B ^ 7 = 1) (hB1 : B ≠ 1)
    (hBsp : Bᵀ * fromBlocks 0 1 (-1) 0 * B = fromBlocks 0 1 (-1) 0)
    (hb : ∀ i, b i ^ 3 = 1)
    (hAB : diagonal (Sum.elim (fun i => (b i : L)) fun i => ((b i)⁻¹ : Lˣ)) * B =
      B * diagonal (Sum.elim (fun i => (b i : L)) fun i => ((b i)⁻¹ : Lˣ))) :
    (∀ i, b i = 1) ∨ ∀ i, b i ≠ 1 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
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
  have h7ne : (7 : L) ≠ 0 := by
    intro h
    have h' : ((7 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L 2] at h'
    norm_num at h'
  obtain ⟨μ, v, hv, hBv, hμ1⟩ := exists_eigenvalue_ne_one_of_pow_seven h7ne h7 hB1
  have hpowv : ∀ k : ℕ, B ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hBv, mulVec_smul, ih, smul_smul, pow_succ']
  have hμ7 : μ ^ 7 = 1 := by
    have h := hpowv 7
    rw [h7, one_mulVec] at h
    by_contra hne
    apply hv
    have h' : (μ ^ 7 - 1) • v = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne)
  have hμo : orderOf μ = 7 := orderOf_eq_prime hμ7 hμ1
  have hprim : IsPrimitiveRoot μ 7 := hμo ▸ IsPrimitiveRoot.orderOf μ
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow (by norm_num)] at hμ7
    exact zero_ne_one hμ7
  have hμinv : μ⁻¹ = μ ^ 6 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hμ7])
  have hAB' : A * B = B * A := hAB
  obtain ⟨c, w, hw, hBw, hAw⟩ := exists_common_eigenvector hAB' hv hBv
  obtain ⟨u, hu, hBu⟩ : ∃ u : Fin 3 ⊕ Fin 3 → L, u ≠ 0 ∧ B *ᵥ u = μ⁻¹ • u := by
    set J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L := fromBlocks 0 1 (-1) 0 with hJ
    have hJJ : J * J = -1 := by
      rw [hJ, fromBlocks_multiply]
      simp [fromBlocks_neg, ← fromBlocks_one]
    have hJw : Bᵀ *ᵥ (J *ᵥ w) = μ⁻¹ • (J *ᵥ w) := by
      have h1 : Bᵀ *ᵥ (J *ᵥ (B *ᵥ w)) = J *ᵥ w := by
        rw [mulVec_mulVec, mulVec_mulVec, hBsp]
      rw [hBw, mulVec_smul, mulVec_smul] at h1
      calc Bᵀ *ᵥ (J *ᵥ w) = μ⁻¹ • (μ • Bᵀ *ᵥ (J *ᵥ w)) := by
            rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
        _ = μ⁻¹ • (J *ᵥ w) := by rw [h1]
    have hJw0 : J *ᵥ w ≠ 0 := by
      intro h
      apply hw
      have h2 : J *ᵥ (J *ᵥ w) = 0 := by rw [h, mulVec_zero]
      rw [mulVec_mulVec, hJJ, neg_mulVec, one_mulVec, neg_eq_zero] at h2
      exact h2
    have hdet : (B - μ⁻¹ • (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) L)).det = 0 := by
      rw [← det_transpose, transpose_sub, transpose_smul, transpose_one]
      exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨J *ᵥ w, hJw0, by
        rw [sub_mulVec, hJw, smul_mulVec, one_mulVec, sub_self]⟩
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨u, hu, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hu0
    exact hu0
  obtain ⟨c', w', hw', hBw', hAw'⟩ := exists_common_eigenvector hAB' hu hBu
  have hval : ∀ {γ : L} {x : Fin 3 ⊕ Fin 3 → L}, x ≠ 0 → A *ᵥ x = γ • x → γ ^ 3 = 1 := by
    intro γ x hx hAx
    obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (funext hcon)
    have hyk : y k = γ := by
      by_contra hne
      exact hk (apply_eq_zero_of_diagonal_mulVec hAx hne)
    rw [← hyk]
    exact hy3 k
  have hc3 := hval hw hAw
  have hc'3 := hval hw' hAw'
  have hφc : φ c = c := by rw [hφ, pow_succ, hc3, one_mul]
  have hφc' : φ c' = c' := by rw [hφ, pow_succ, hc'3, one_mul]
  obtain ⟨hw₁, hBw₁, hAw₁⟩ := frobenius_eigenvector φ hBφ hAφ hw hBw hAw
  rw [hφc] at hAw₁
  obtain ⟨hw₂, hBw₂, hAw₂⟩ := frobenius_eigenvector φ hBφ hAφ hw₁ hBw₁ hAw₁
  rw [hφc] at hAw₂
  obtain ⟨hw'₁, hBw'₁, hAw'₁⟩ := frobenius_eigenvector φ hBφ hAφ hw' hBw' hAw'
  rw [hφc'] at hAw'₁
  obtain ⟨hw'₂, hBw'₂, hAw'₂⟩ := frobenius_eigenvector φ hBφ hAφ hw'₁ hBw'₁ hAw'₁
  rw [hφc'] at hAw'₂
  have e1 : φ μ = μ ^ 4 := hφ μ
  have e2 : φ (φ μ) = μ ^ 2 := by
    rw [hφ, hφ, ← pow_mul, show 4 * 4 = 7 * 2 + 2 by norm_num, pow_add, pow_mul, hμ7, one_pow,
      one_mul]
  have e3 : μ⁻¹ = μ ^ 6 := hμinv
  have e4 : φ μ⁻¹ = μ ^ 3 := by
    rw [hμinv, hφ, ← pow_mul, show 6 * 4 = 7 * 3 + 3 by norm_num, pow_add, pow_mul, hμ7, one_pow,
      one_mul]
  have e5 : φ (φ μ⁻¹) = μ ^ 5 := by
    rw [e4, hφ, ← pow_mul, show 3 * 4 = 7 + 5 by norm_num, pow_add, hμ7, one_mul]
  rw [e2] at hBw₂
  rw [e1] at hBw₁
  rw [e5] at hBw'₂
  rw [e4] at hBw'₁
  rw [e3] at hBw'
  set ex : Fin 6 → ℕ := ![1, 4, 2, 6, 3, 5] with hex
  set lam : Fin 6 → L := fun i => μ ^ ex i with hlam
  set vec : Fin 6 → (Fin 3 ⊕ Fin 3 → L) :=
    ![w, φ ∘ w, φ ∘ (φ ∘ w), w', φ ∘ w', φ ∘ (φ ∘ w')] with hvec
  have hexlt : ∀ i, ex i < 7 := by decide
  have hexinj : ∀ i j, ex i = ex j → i = j := by decide
  have hlaminj : Function.Injective lam := fun i j h =>
    hexinj i j (hprim.pow_inj (hexlt i) (hexlt j) h)
  have hvecB : ∀ i, B *ᵥ vec i = lam i • vec i := by
    intro i
    fin_cases i
    · simpa [hvec, hlam, hex] using hBw
    · simpa [hvec, hlam, hex] using hBw₁
    · simpa [hvec, hlam, hex] using hBw₂
    · simpa [hvec, hlam, hex] using hBw'
    · simpa [hvec, hlam, hex] using hBw'₁
    · simpa [hvec, hlam, hex] using hBw'₂
  have hvec0 : ∀ i, vec i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [hvec] using hw
    · simpa [hvec] using hw₁
    · simpa [hvec] using hw₂
    · simpa [hvec] using hw'
    · simpa [hvec] using hw'₁
    · simpa [hvec] using hw'₂
  have hli : LinearIndependent L vec :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' B) lam hlaminj vec fun i => by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact ⟨hvecB i, hvec0 i⟩
  set I := Finset.univ.filter (fun k => y k = c) with hI
  set I' := Finset.univ.filter (fun k => y k = c') with hI'
  have hsuppc : ∀ {x : Fin 3 ⊕ Fin 3 → L}, A *ᵥ x = c • x → ∀ k, k ∉ I → x k = 0 := by
    intro x hx k hk
    refine apply_eq_zero_of_diagonal_mulVec hx ?_
    simpa [hI] using hk
  have hsuppc' : ∀ {x : Fin 3 ⊕ Fin 3 → L}, A *ᵥ x = c' • x → ∀ k, k ∉ I' → x k = 0 := by
    intro x hx k hk
    refine apply_eq_zero_of_diagonal_mulVec hx ?_
    simpa [hI'] using hk
  have hcardU : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by simp
  by_cases hcc : c = c'
  ·
    left
    have h6 : 6 ≤ I.card := by
      have := card_le_of_linearIndependent_supported hli I (by
        intro j k hk
        fin_cases j
        · exact hsuppc hAw k hk
        · exact hsuppc hAw₁ k hk
        · exact hsuppc hAw₂ k hk
        · exact hsuppc (hcc ▸ hAw') k hk
        · exact hsuppc (hcc ▸ hAw'₁) k hk
        · exact hsuppc (hcc ▸ hAw'₂) k hk)
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
  ·
    have h3 : 3 ≤ I.card := by
      have hsub : LinearIndependent L ![w, φ ∘ w, φ ∘ (φ ∘ w)] := by
        have := hli.comp (fun i : Fin 3 => (Fin.castLE (by norm_num) i : Fin 6))
          (fun i j h => Fin.castLE_injective _ h)
        convert this using 1
        funext i
        fin_cases i <;> simp [hvec]
      have := card_le_of_linearIndependent_supported hsub I (by
        intro j k hk
        fin_cases j
        · exact hsuppc hAw k hk
        · exact hsuppc hAw₁ k hk
        · exact hsuppc hAw₂ k hk)
      simpa using this
    have h3' : 3 ≤ I'.card := by
      have hsub : LinearIndependent L ![w', φ ∘ w', φ ∘ (φ ∘ w')] := by
        have := hli.comp (fun i : Fin 3 => (Fin.natAdd 3 i : Fin 6))
          (fun i j h => (Fin.natAdd_inj 3).mp h)
        convert this using 1
        funext i
        fin_cases i <;> simp [hvec]
      have := card_le_of_linearIndependent_supported hsub I' (by
        intro j k hk
        fin_cases j
        · exact hsuppc' hAw' k hk
        · exact hsuppc' hAw'₁ k hk
        · exact hsuppc' hAw'₂ k hk)
      simpa using this
    have hdisj : Disjoint I I' := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [hI, hI', Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
      exact hcc (hk.symm.trans hk')
    have hall : ∀ k, y k = c ∨ y k = c' := by
      have hU : I ∪ I' = Finset.univ := Finset.eq_univ_of_card _ (by
        rw [Finset.card_union_of_disjoint hdisj]
        have := Finset.card_le_univ (I ∪ I')
        rw [Finset.card_union_of_disjoint hdisj, hcardU] at this
        rw [hcardU]
        omega)
      intro k
      have := Finset.mem_univ k
      rw [← hU, Finset.mem_union, hI, hI', Finset.mem_filter, Finset.mem_filter] at this
      rcases this with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2
    by_cases hb1 : ∀ i, b i = 1
    · exact Or.inl hb1
    · right
      push Not at hb1
      obtain ⟨j, hj⟩ := hb1
      have hj1 : (b j : L) ≠ 1 := fun h => hj (Units.ext h)
      have hj1' : ((b j)⁻¹ : Lˣ).val ≠ 1 := by
        intro h
        apply hj
        have : (b j)⁻¹ = 1 := Units.ext h
        rw [← inv_inv (b j), this, inv_one]
      have hjne : (b j : L) ≠ ((b j)⁻¹ : Lˣ) := by
        intro h
        apply hj
        have h2 : b j = (b j)⁻¹ := Units.ext h
        have hsq : b j ^ 2 = 1 := by
          rw [sq]
          nth_rewrite 2 [h2]
          exact mul_inv_cancel (b j)
        calc b j = b j ^ 3 * (b j ^ 2)⁻¹ := by group
          _ = 1 := by rw [hb j, hsq, inv_one, one_mul]
      have hl := hall (Sum.inl j)
      have hr := hall (Sum.inr j)
      simp only [hy, Sum.elim_inl, Sum.elim_inr] at hl hr
      have hc1 : c ≠ 1 ∧ c' ≠ 1 := by
        rcases hl with hl | hl <;> rcases hr with hr | hr
        · exact absurd (hl.trans hr.symm) hjne
        · exact ⟨hl ▸ hj1, hr ▸ hj1'⟩
        · exact ⟨hr ▸ hj1', hl ▸ hj1⟩
        · exact absurd (hl.trans hr.symm) hjne
      intro i hi
      have h := hall (Sum.inl i)
      simp only [hy, Sum.elim_inl, hi, Units.val_one] at h
      rcases h with h | h
      · exact hc1.1 h.symm
      · exact hc1.2 h.symm

theorem sp_trivial_or_regular_of_commute_pow_seven' {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F} {b : Fin 3 → Fˣ}
    (h7 : B ^ 7 = 1) (hB1 : B ≠ 1)
    (hBsp : Bᵀ * fromBlocks 0 1 (-1) 0 * B = fromBlocks 0 1 (-1) 0)
    (hb : ∀ i, b i ^ 3 = 1)
    (hAB : diagonal (Sum.elim (fun i => (b i : F)) fun i => ((b i)⁻¹ : Fˣ)) * B =
      B * diagonal (Sum.elim (fun i => (b i : F)) fun i => ((b i)⁻¹ : Fˣ))) :
    (∀ i, b i = 1) ∨ ∀ i, b i ≠ 1 := by
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
  have hJ : ι (fromBlocks 0 1 (-1) 0) = fromBlocks 0 1 (-1) 0 := by
    rw [hι, RingHom.mapMatrix_apply]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.one_apply, apply_ite]
  have hres := sp_trivial_or_regular_of_commute_pow_seven (L := L) (B := ι B) (b := b')
    (by
      ext i j
      simp only [hι, RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [← map_pow, hpow4])
    (by rw [← map_pow, h7, map_one])
    (fun h => hB1 (hinj (by rw [h, map_one])))
    (by
      have h := congrArg ι hBsp
      rw [map_mul, map_mul, hJ] at h
      convert h using 3
      rw [hι, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, transpose_map])
    (fun i => by rw [hb', ← map_pow, hb i, map_one])
    (by rw [← hdiag, ← map_mul, ← map_mul, hAB])
  have hb'1 : ∀ i, b' i = 1 ↔ b i = 1 := by
    intro i
    constructor
    · intro h
      apply Units.ext
      apply (algebraMap F L).injective
      have := congrArg Units.val h
      simpa [hb'] using this
    · intro h
      simp only [hb', h, map_one]
  rcases hres with h | h
  · exact Or.inl fun i => (hb'1 i).mp (h i)
  · exact Or.inr fun i hi => h i ((hb'1 i).mpr hi)

end CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV
