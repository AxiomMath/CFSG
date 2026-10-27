module

public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

namespace CFSG.StandardType.TraceFrame

open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LocalAnalysis.ComponentInitial Matrix

lemma card_two_eq_zero_or_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (k : K) : k = 0 ∨ k = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have : DecidableEq K := Classical.decEq K
  have h2 : Fintype.card K ≤ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have huniv := Finset.univ_of_card_le_two (R := K) h2
  have hk : k ∈ (Finset.univ : Finset K) := Finset.mem_univ k
  rw [huniv] at hk
  simpa using hk

lemma card_two_mul_self {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (k : K) : k * k = k := by
  rcases card_two_eq_zero_or_one hK k with h | h <;> simp [h]

lemma tau_algebraMap {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) (τ : M ≃+* M) (k : K) :
    τ (algebraMap K M k) = algebraMap K M k := by
  rcases card_two_eq_zero_or_one hK k with h | h <;> simp [h]

@[expose] noncomputable def tauAlg {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) {τ : M ≃+* M} : M ≃ₐ[K] M :=
  AlgEquiv.ofRingEquiv (f := τ) fun k => tau_algebraMap hK τ k

lemma trace_tau {K M : Type} [Field K] [Finite K] [Field M] [Finite M] [Algebra K M]
    (hK : Nat.card K = 2) {τ : M ≃+* M} (y : M) :
    Algebra.trace K M (τ y) = Algebra.trace K M y :=
  Algebra.trace_eq_of_algEquiv (tauAlg (τ := τ) hK) y

lemma eq_zero_of_trace_mul_eq_zero {K M : Type} [Field K] [Finite K] [Field M]
    [Finite M] [Algebra K M] {y : M}
    (h : ∀ μ : M, Algebra.trace K M (μ * y) = 0) : y = 0 := by
  refine (traceForm_nondegenerate K M).1 y ?_
  intro μ
  rw [Algebra.traceForm_apply]
  simpa [mul_comm] using h μ

lemma finrank_eq_two {K M : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] (hK : Nat.card K = 2) (hM : Nat.card M = 4) :
    Module.finrank K M = 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype M := Fintype.ofFinite M
  have h := Module.card_eq_pow_finrank (K := K) (V := M)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hM] at h
  exact Nat.pow_right_injective (le_refl 2) h.symm

lemma notMem_algebraMap_of_sq_ne {K M : Type} [Field K] [Finite K] [Field M]
    [Algebra K M] (hK : Nat.card K = 2) {c : M} (hc : c ^ 2 ≠ c) :
    c ∉ Set.range (algebraMap K M) := by
  rintro ⟨k, rfl⟩
  apply hc
  rw [← map_pow, pow_two, card_two_mul_self hK k]

lemma exists_eq_algebraMap_add_mul {K M : Type} [Field K] [Finite K] [Field M]
    [Finite M] [Algebra K M] (hK : Nat.card K = 2) (hM : Nat.card M = 4) {c : M}
    (hc : c ^ 2 ≠ c) :
    ∀ m : M, ∃ a b : K, m = algebraMap K M a + algebraMap K M b * c := by
  have hfr : Module.finrank K M = 2 := finrank_eq_two hK hM
  have hcK : c ∉ Set.range (algebraMap K M) := notMem_algebraMap_of_sq_ne hK hc
  have h1c : LinearIndependent K ![1, c] := by
    rw [LinearIndependent.pair_iff']
    · intro a ha
      exact hcK ⟨a, by simpa [Algebra.algebraMap_eq_smul_one] using ha⟩
    · exact one_ne_zero
  have hrange : Set.range ![1, c] = ({1, c} : Set M) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have htop : Submodule.span K (Set.range ![1, c]) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card h1c, hfr]
    simp
  intro m
  have hm : m ∈ Submodule.span K ({1, c} : Set M) := by
    rw [← hrange, htop]
    exact Submodule.mem_top
  rw [Submodule.mem_span_pair] at hm
  obtain ⟨a, b, hab⟩ := hm
  refine ⟨a, b, ?_⟩
  have hb : b • c = (b • (1 : M)) * c := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← hb]
  exact hab.symm

@[expose] noncomputable def matVecEquiv {n : ℕ} {M : Type} [Field M] (A : GL (Fin n) M) :
    (Fin n → M) ≃ₗ[M] (Fin n → M) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv M (Fin n → M))
    (Matrix.GeneralLinearGroup.toLin A)

lemma matVecEquiv_apply {n : ℕ} {M : Type} [Field M] (A : GL (Fin n) M)
    (v : Fin n → M) :
    matVecEquiv A v = (A : Matrix (Fin n) (Fin n) M) *ᵥ v := by
  rw [matVecEquiv, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]

@[expose] noncomputable def rhoEquiv {K M U V : Type} [Field K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    (Φ : ((Fin n → M) × U) ≃ₗ[K] V) (A : GL (Fin n) M) : V ≃ₗ[K] V :=
  (Φ.symm.trans (((matVecEquiv A).restrictScalars K).prodCongr
    (LinearEquiv.refl K U))).trans Φ

lemma rhoEquiv_apply {K M U V : Type} [Field K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (A : GL (Fin n) M) (d : Fin n → M) (w : U) :
    rhoEquiv Φ A (Φ (d, w)) = Φ ((A : Matrix (Fin n) (Fin n) M) *ᵥ d, w) := by
  rw [rhoEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  simp [LinearEquiv.prodCongr_apply, matVecEquiv_apply]

lemma rhoEquiv_mul {K M U V : Type} [Field K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (A B : GL (Fin n) M) :
    rhoEquiv Φ (A * B) = rhoEquiv Φ A * rhoEquiv Φ B := by
  ext v
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [LinearEquiv.mul_apply, rhoEquiv_apply, rhoEquiv_apply, rhoEquiv_apply,
    Matrix.mulVec_mulVec, ← Units.val_mul]

lemma rhoEquiv_one {K M U V : Type} [Field K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} :
    rhoEquiv Φ (1 : GL (Fin n) M) = 1 := by
  ext v
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [rhoEquiv_apply]
  simp

@[expose] noncomputable def rhoGL {K M U V : Type} [Field K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    (Φ : ((Fin n → M) × U) ≃ₗ[K] V) (A : GL (Fin n) M) :
    LinearMap.GeneralLinearGroup K V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm (rhoEquiv Φ A)

lemma coe_rhoGL {K M U V : Type} [Field K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (A : GL (Fin n) M) :
    ((rhoGL Φ A : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
      (rhoEquiv Φ A : V →ₗ[K] V) := by
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap (R := K) (M := V)
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm (rhoEquiv Φ A))).symm

@[expose] noncomputable def frobLin {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) {τ : M ≃+* M} (_hτ : ∀ y, τ (τ y) = y) {n : ℕ} (i : Fin n) :
    (Fin n → M) →ₗ[K] (Fin n → M) :=
  LinearMap.pi fun j =>
    if j = i then (tauAlg (τ := τ) hK).toLinearMap.comp (LinearMap.proj i) else LinearMap.proj j

lemma frobLin_apply {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) {τ : M ≃+* M} (hτ : ∀ y, τ (τ y) = y) {n : ℕ} (i : Fin n)
    (d : Fin n → M) :
    frobLin hK hτ i d = Function.update d i (τ (d i)) := by
  ext j
  rw [frobLin, LinearMap.pi_apply]
  by_cases h : j = i
  · subst h
    simp [tauAlg, Function.update_self]
  · simp [h]

lemma frobLin_invol {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) {τ : M ≃+* M} (hτ : ∀ y, τ (τ y) = y) {n : ℕ} (i : Fin n)
    (d : Fin n → M) :
    frobLin hK hτ i (frobLin hK hτ i d) = d := by
  ext j
  by_cases h : j = i
  · subst h
    rw [frobLin_apply, Function.update_self, frobLin_apply, Function.update_self, hτ]
  · rw [frobLin_apply, Function.update_of_ne h, frobLin_apply, Function.update_of_ne h]

@[expose] noncomputable def frobEquiv {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) {τ : M ≃+* M} (hτ : ∀ y, τ (τ y) = y) {n : ℕ} (i : Fin n) :
    (Fin n → M) ≃ₗ[K] (Fin n → M) :=
  LinearEquiv.ofLinearMap (frobLin hK hτ i) (frobLin hK hτ i)
    (by
      apply LinearMap.ext
      intro d
      change frobLin hK hτ i (frobLin hK hτ i d) = d
      exact frobLin_invol hK hτ i d)
    (by
      apply LinearMap.ext
      intro d
      change frobLin hK hτ i (frobLin hK hτ i d) = d
      exact frobLin_invol hK hτ i d)

lemma frobEquiv_apply {K M : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    (hK : Nat.card K = 2) {τ : M ≃+* M} (hτ : ∀ y, τ (τ y) = y) {n : ℕ} (i : Fin n)
    (d : Fin n → M) :
    frobEquiv hK hτ i d = Function.update d i (τ (d i)) := by
  rw [frobEquiv, LinearEquiv.coe_ofLinearMap, frobLin_apply]

@[expose] noncomputable def frobEquivV {K M U V : Type} [Field K] [Finite K] [Field M]
    [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    (hK : Nat.card K = 2) {τ : M ≃+* M} (hτ : ∀ y, τ (τ y) = y)
    (Φ : ((Fin n → M) × U) ≃ₗ[K] V) (i : Fin n) : V ≃ₗ[K] V :=
  (Φ.symm.trans (((frobEquiv hK hτ i).prodCongr (LinearEquiv.refl K U)))).trans Φ

lemma frobEquivV_apply {K M U V : Type} [Field K] [Finite K] [Field M]
    [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {τ : M ≃+* M} (hK : Nat.card K = 2) {hτ : ∀ y, τ (τ y) = y}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (i : Fin n) (d : Fin n → M) (w : U) :
    frobEquivV hK hτ Φ i (Φ (d, w)) = Φ (Function.update d i (τ (d i)), w) := by
  rw [frobEquivV, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  simp [LinearEquiv.prodCongr_apply, frobEquiv_apply]

lemma frobEquivV_mul_self {K M U V : Type} [Field K] [Finite K] [Field M]
    [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {τ : M ≃+* M} (hK : Nat.card K = 2) {hτ : ∀ y, τ (τ y) = y}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (i : Fin n) :
    frobEquivV hK hτ Φ i * frobEquivV hK hτ Φ i = 1 := by
  ext v
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [LinearEquiv.mul_apply, frobEquivV_apply, frobEquivV_apply, Function.update_idem,
    Function.update_self, hτ, Function.update_eq_self]
  rfl

@[expose] noncomputable def frobUnit {K M U V : Type} [Field K] [Finite K] [Field M]
    [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {τ : M ≃+* M} (hK : Nat.card K = 2) (hτ : ∀ y, τ (τ y) = y)
    (Φ : ((Fin n → M) × U) ≃ₗ[K] V) (i : Fin n) : LinearMap.GeneralLinearGroup K V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm (frobEquivV hK hτ Φ i)

lemma coe_frobUnit {K M U V : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {τ : M ≃+* M} (hK : Nat.card K = 2) (hτ : ∀ y, τ (τ y) = y)
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (i : Fin n) :
    ((frobUnit hK hτ Φ i : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
      (frobEquivV hK hτ Φ i : V →ₗ[K] V) := by
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap (R := K) (M := V)
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm (frobEquivV hK hτ Φ i))).symm

lemma coe_frobUnit_apply {K M U V : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {τ : M ≃+* M} (hK : Nat.card K = 2) (hτ : ∀ y, τ (τ y) = y)
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (i : Fin n) (x : V) :
    ((frobUnit hK hτ Φ i : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x =
      frobEquivV hK hτ Φ i x := by
  rw [coe_frobUnit]
  rfl

lemma frobUnit_mul_self {K M U V : Type} [Field K] [Finite K] [Field M]
    [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {τ : M ≃+* M} (hK : Nat.card K = 2) (hτ : ∀ y, τ (τ y) = y)
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (i : Fin n) :
    frobUnit hK hτ Φ i * frobUnit hK hτ Φ i = 1 := by
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).injective
  rw [map_mul, map_one]
  exact frobEquivV_mul_self hK i

lemma frobUnit_inv {K M U V : Type} [Field K] [Finite K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {τ : M ≃+* M} (hK : Nat.card K = 2) (hτ : ∀ y, τ (τ y) = y)
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (i : Fin n) :
    (frobUnit hK hτ Φ i)⁻¹ = frobUnit hK hτ Φ i :=
  (mul_eq_one_iff_inv_eq).mp (frobUnit_mul_self hK hτ i)

end CFSG.StandardType.TraceFrame

end
