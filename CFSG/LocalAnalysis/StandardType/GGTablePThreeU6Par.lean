module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix CFSG.AGLEmbedding

private noncomputable def hf {K : Type} [Field K] (q : ℕ) (u v : Fin 6 → K) : K :=
  ∑ i, u i ^ q * v i

private lemma sum_pow_two_pow {K : Type} [Field K] [CharP K 2] {f : ℕ} {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (g : ι → K) :
    (∑ i ∈ s, g i) ^ (2 ^ f) = ∑ i ∈ s, (g i) ^ (2 ^ f) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char_pow, ih]

private lemma hf_add_right {K : Type} [Field K] (q : ℕ) (u v v' : Fin 6 → K) :
    hf q u (v + v') = hf q u v + hf q u v' := by
  simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma hf_smul_left {K : Type} [Field K] (q : ℕ) (c : K) (u v : Fin 6 → K) :
    hf q (c • u) v = c ^ q * hf q u v := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma hf_smul_right {K : Type} [Field K] (q : ℕ) (c : K) (u v : Fin 6 → K) :
    hf q u (c • v) = c * hf q u v := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem X3subC_irreducible {K : Type} [Field K] {lam : K}
    (hlam : ∀ μ : K, μ ^ 3 ≠ lam) :
    Irreducible (Polynomial.X ^ 3 - Polynomial.C lam : Polynomial K) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three hlam

private lemma aeval_X3subC {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {T : V →ₗ[K] V} {lam : K} (hT : T ^ 3 = lam • 1) :
    Polynomial.aeval T (Polynomial.X ^ 3 - Polynomial.C lam : Polynomial K) = 0 := by
  rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one', hT, sub_self]

private lemma monic_X3subC {K : Type} [Field K] {lam : K} :
    (Polynomial.X ^ 3 - Polynomial.C lam : Polynomial K).Monic :=
  Polynomial.monic_X_pow_sub_C _ (by norm_num)

private lemma minpoly_eq_X3subC {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [Nontrivial V] {T : V →ₗ[K] V} {lam : K} (hlam : ∀ μ : K, μ ^ 3 ≠ lam)
    (hT : T ^ 3 = lam • 1) :
    minpoly K T = Polynomial.X ^ 3 - Polynomial.C lam :=
  (minpoly.eq_of_irreducible_of_monic (X3subC_irreducible hlam) (aeval_X3subC hT)
    (monic_X3subC (lam := lam))).symm

private lemma aeval_eq_zero_iff_dvd {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [Nontrivial V] {T : V →ₗ[K] V} {lam : K} (hlam : ∀ μ : K, μ ^ 3 ≠ lam)
    (hT : T ^ 3 = lam • 1) (p : Polynomial K) :
    Polynomial.aeval T p = 0 ↔ Polynomial.X ^ 3 - Polynomial.C lam ∣ p := by
  have hker : RingHom.ker (Polynomial.aeval T) =
      Ideal.span {Polynomial.X ^ 3 - Polynomial.C lam} := by
    rw [minpoly.ker_aeval_eq_span_minpoly, minpoly_eq_X3subC hlam hT]
  rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]

private lemma aeval_mul_eq_one_of_not_dvd {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [Nontrivial V] {T : V →ₗ[K] V} {lam : K} (hlam : ∀ μ : K, μ ^ 3 ≠ lam)
    (hT : T ^ 3 = lam • 1) {p : Polynomial K}
    (hp : ¬ (Polynomial.X ^ 3 - Polynomial.C lam) ∣ p) :
    ∃ q : Polynomial K, Polynomial.aeval T q * Polynomial.aeval T p = 1 := by
  have hcop : IsCoprime (Polynomial.X ^ 3 - Polynomial.C lam) p :=
    (X3subC_irreducible hlam).coprime_iff_not_dvd.mpr hp
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨b, ?_⟩
  have h1 : Polynomial.aeval T a * Polynomial.aeval T (Polynomial.X ^ 3 - Polynomial.C lam)
      + Polynomial.aeval T b * Polynomial.aeval T p = 1 := by
    rw [← map_mul, ← map_mul, ← map_add, hab, map_one]
  rw [aeval_X3subC hT, mul_zero, zero_add] at h1
  exact h1

private lemma pow_mem_of_stable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {T : V →ₗ[K] V} {S : Submodule K V} (hS : ∀ y ∈ S, T y ∈ S) (n : ℕ) {y : V}
    (hy : y ∈ S) : (T ^ n) y ∈ S := by
  induction n with
  | zero => simpa using hy
  | succ n ih => rw [pow_succ']; exact hS _ ih

private lemma range_vec3 {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (T : V →ₗ[K] V) (w : V) : Set.range ![w, T w, (T ^ 2) w] = {w, T w, (T ^ 2) w} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

private noncomputable def tline {K : Type} [Field K] (T : (Fin 6 → K) →ₗ[K] (Fin 6 → K))
    (w : Fin 6 → K) : Submodule K (Fin 6 → K) :=
  Submodule.span K {w, T w, (T ^ 2) w}

private lemma mem_tline_iff {K : Type} [Field K] {T : (Fin 6 → K) →ₗ[K] (Fin 6 → K)}
    (w x : Fin 6 → K) :
    x ∈ tline T w ↔ ∃ a b c : K, x = a • w + b • T w + c • (T ^ 2) w := by
  rw [tline, Submodule.mem_span_insert]
  constructor
  · rintro ⟨a, z, hz, rfl⟩
    rw [Submodule.mem_span_insert] at hz
    obtain ⟨b, z', hz', rfl⟩ := hz
    rw [Submodule.mem_span_singleton] at hz'
    obtain ⟨c, rfl⟩ := hz'
    exact ⟨a, b, c, by module⟩
  · rintro ⟨a, b, c, rfl⟩
    refine ⟨a, b • T w + c • (T ^ 2) w, ?_, by module⟩
    rw [Submodule.mem_span_insert]
    exact ⟨b, c • (T ^ 2) w, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩, by module⟩

private lemma tline_le_of_mem {K : Type} [Field K] {T : (Fin 6 → K) →ₗ[K] (Fin 6 → K)}
    {W : Submodule K (Fin 6 → K)} (hW : ∀ y ∈ W, T y ∈ W) {w : Fin 6 → K}
    (hw : w ∈ W) : tline T w ≤ W := by
  rw [tline]
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hw
  · exact hW w hw
  · exact hW _ (hW w hw)

private lemma aeval_eq_zero_of_natDegree_le_two {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [Nontrivial V] {T : V →ₗ[K] V} {lam : K}
    (hlam : ∀ μ : K, μ ^ 3 ≠ lam) (hT : T ^ 3 = lam • 1)
    {p : Polynomial K} (hp : p.natDegree ≤ 2) {w : V} (hw : w ≠ 0)
    (hpw : Polynomial.aeval T p w = 0) : p = 0 := by
  by_contra hp0
  have hdvd : ¬ (Polynomial.X ^ 3 - Polynomial.C lam) ∣ p := by
    intro hd
    have hle := Polynomial.natDegree_le_of_dvd hd hp0
    rw [Polynomial.natDegree_X_pow_sub_C] at hle
    omega
  obtain ⟨q, hq⟩ := aeval_mul_eq_one_of_not_dvd hlam hT hdvd
  have : w = 0 := by
    calc w = (1 : V →ₗ[K] V) w := rfl
      _ = (Polynomial.aeval T q * Polynomial.aeval T p) w := by rw [hq]
      _ = Polynomial.aeval T q (Polynomial.aeval T p w) := rfl
      _ = 0 := by rw [hpw, map_zero]
  exact hw this

private lemma tline_linearIndependent {K : Type} [Field K] {T : (Fin 6 → K) →ₗ[K] (Fin 6 → K)}
    {lam : K} (hlam : ∀ μ : K, μ ^ 3 ≠ lam) (hT : T ^ 3 = lam • 1)
    {w : Fin 6 → K} (hw : w ≠ 0) :
    LinearIndependent K ![w, T w, (T ^ 2) w] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let p : Polynomial K := Polynomial.C (g 0) + Polynomial.C (g 1) * Polynomial.X
    + Polynomial.C (g 2) * Polynomial.X ^ 2
  have hpw : Polynomial.aeval T p w = 0 := by
    have hsum : (∑ j : Fin 3, g j • ![w, T w, (T ^ 2) w] j)
        = g 0 • w + g 1 • T w + g 2 • (T ^ 2) w := by
      simp [Fin.sum_univ_three]
    have hpval : Polynomial.aeval T p w = g 0 • w + g 1 • T w + g 2 • (T ^ 2) w := by
      dsimp only [p]
      simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow,
        Algebra.algebraMap_eq_smul_one', LinearMap.add_apply, Module.End.mul_apply,
        LinearMap.smul_apply, Module.End.one_apply]
    rw [hpval, ← hsum, hg]
  have hp2 : p.natDegree ≤ 2 := by
    dsimp only [p]
    compute_degree!
  have hp0 : p = 0 := aeval_eq_zero_of_natDegree_le_two hlam hT hp2 hw hpw
  have h0 : g 0 = 0 := by
    have := congrArg (fun p : Polynomial K => p.coeff 0) hp0
    simpa [p] using this
  have h1 : g 1 = 0 := by
    have := congrArg (fun p : Polynomial K => p.coeff 1) hp0
    simpa [p] using this
  have h2 : g 2 = 0 := by
    have := congrArg (fun p : Polynomial K => p.coeff 2) hp0
    simpa [p] using this
  fin_cases i <;> assumption

private lemma tline_finrank {K : Type} [Field K] {T : (Fin 6 → K) →ₗ[K] (Fin 6 → K)}
    {lam : K} (hlam : ∀ μ : K, μ ^ 3 ≠ lam) (hT : T ^ 3 = lam • 1)
    {w : Fin 6 → K} (hw : w ≠ 0) : Module.finrank K (tline T w) = 3 := by
  rw [tline, ← range_vec3 T w]
  exact finrank_span_eq_card (tline_linearIndependent hlam hT hw)

private lemma apply_eq_zero_on_tline {K : Type} [Field K]
    {T S : (Fin 6 → K) →ₗ[K] (Fin 6 → K)} (hST : S * T = T * S) {w0 : Fin 6 → K}
    (hw : S w0 = 0) : ∀ w ∈ tline T w0, S w = 0 := by
  intro w hw'
  rw [mem_tline_iff] at hw'
  obtain ⟨b0, b1, b2, rfl⟩ := hw'
  have h1 : S (T w0) = 0 := by
    calc S (T w0) = (S * T) w0 := rfl
      _ = (T * S) w0 := by rw [hST]
      _ = T (S w0) := rfl
      _ = 0 := by rw [hw, map_zero]
  have h2 : S ((T ^ 2) w0) = 0 := by
    change S (T (T w0)) = 0
    calc S (T (T w0)) = (S * T) (T w0) := rfl
      _ = (T * S) (T w0) := by rw [hST]
      _ = T (S (T w0)) := rfl
      _ = 0 := by rw [h1, map_zero]
  rw [map_add, map_add, map_smul, map_smul, map_smul, hw, h1, h2]
  simp

private lemma aeval_quad_general {K : Type} [Field K] {A : Type} [Semiring A] [Algebra K A]
    (x : A) (a0 a1 a2 : K) :
    Polynomial.aeval x (Polynomial.C a0 + Polynomial.C a1 * Polynomial.X
        + Polynomial.C a2 * Polynomial.X ^ 2) = a0 • 1 + a1 • x + a2 • x ^ 2 := by
  rw [Polynomial.aeval_add, Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_mul,
    Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C, map_pow,
    Polynomial.aeval_X]
  simp only [Algebra.algebraMap_eq_smul_one', smul_mul_assoc, one_mul]

private noncomputable def frob6 {K : Type} [Field K] (q : ℕ) (x : Fin 6 → K) : Fin 6 → K :=
  fun i => x i ^ q

private noncomputable def dotBilin {K : Type} [Field K] :
    LinearMap.BilinForm K (Fin 6 → K) :=
  Matrix.toBilin' (1 : Matrix (Fin 6) (Fin 6) K)

private lemma dotBilin_apply {K : Type} [Field K] (x y : Fin 6 → K) :
    dotBilin (K := K) x y = ∑ i, x i * y i := by
  rw [dotBilin, Matrix.toBilin'_apply', Matrix.one_mulVec]
  rfl

private lemma dotBilin_nondegenerate {K : Type} [Field K] :
    (dotBilin (K := K)).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  funext i
  have h := congrArg (fun l : (Fin 6 → K) →ₗ[K] K => l (Pi.single i (1 : K))) hx
  simp only [LinearMap.zero_apply] at h
  rw [dotBilin_apply, Finset.sum_eq_single i] at h
  · simpa using h
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma frob6_injective {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) : Function.Injective (frob6 q (K := K)) := by
  haveI : Fintype K := Fintype.ofFinite K
  intro x y hxy
  have hq : ∀ c : K, c ^ (q * q) = c := by
    intro c
    rw [show q * q = Nat.card K by rw [hK]; ring, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  funext i
  have h := congrFun hxy i
  simp only [frob6] at h
  have h2 : (x i ^ q) ^ q = (y i ^ q) ^ q := by rw [h]
  rw [← pow_mul, ← pow_mul] at h2
  simpa only [hq] using h2

private noncomputable def perp {K : Type} [Field K] (q : ℕ)
    (W : Submodule K (Fin 6 → K)) : Submodule K (Fin 6 → K) where
  carrier := {x | ∀ y ∈ W, hf q y x = 0}
  zero_mem' := by
    intro y _
    simp only [hf, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  add_mem' := by
    intro x x' hx hx' y hy
    rw [hf_add_right, hx y hy, hx' y hy, add_zero]
  smul_mem' := by
    intro c x hx y hy
    rw [hf_smul_right, hx y hy, mul_zero]

private lemma mem_perp {K : Type} [Field K] {q : ℕ} {W : Submodule K (Fin 6 → K)}
    {x : Fin 6 → K} : x ∈ perp q W ↔ ∀ y ∈ W, hf q y x = 0 := Iff.rfl

private lemma hf_pow_q {K : Type} [Field K] [CharP K 2] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) {f : ℕ} (hq : q = 2 ^ f) (u v : Fin 6 → K) :
    (hf q u v) ^ q = dotBilin (K := K) u (frob6 q v) := by
  haveI : Fintype K := Fintype.ofFinite K
  subst hq
  have hqq : (2 ^ f) * (2 ^ f) = Nat.card K := by rw [hK]; ring
  rw [hf, dotBilin_apply, sum_pow_two_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [frob6]
  rw [mul_pow, ← pow_mul, hqq, Nat.card_eq_fintype_card, FiniteField.pow_card]

private lemma finrank_perp {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) {f : ℕ} (hq : q = 2 ^ f)
    (W : Submodule K (Fin 6 → K)) :
    Module.finrank K (perp q W) = 6 - Module.finrank K W := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (perp q W) := Fintype.ofFinite _
  haveI : Fintype (dotBilin (K := K).orthogonal W) := Fintype.ofFinite _
  have hq0 : q ≠ 0 := by rw [hq]; positivity
  have hbij : Function.Bijective (frob6 q (K := K)) :=
    ⟨frob6_injective hK, (Finite.injective_iff_surjective.mp (frob6_injective hK))⟩
  let g : perp q W → dotBilin (K := K).orthogonal W := fun x =>
    ⟨frob6 q x.1, by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      have h := x.2 y hy
      rw [← hf_pow_q hK hq y x.1, h, zero_pow hq0]⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x x' hxx'
      have h := congrArg Subtype.val hxx'
      exact Subtype.ext (frob6_injective hK h)
    · intro z
      obtain ⟨x, hx⟩ := hbij.2 z.1
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [mem_perp]
      intro y hy
      have hz := (LinearMap.BilinForm.mem_orthogonal_iff.mp z.2) y hy
      have h : (hf q y x) ^ q = 0 := by
        rw [hf_pow_q hK hq y x, hx]
        exact hz
      exact (pow_eq_zero_iff hq0).mp h
  have hcard : Nat.card (perp q W) = Nat.card (dotBilin (K := K).orthogonal W) :=
    Nat.card_eq_of_bijective g hg
  have h1 : Fintype.card (perp q W) = Fintype.card K ^ Module.finrank K (perp q W) :=
    Module.card_eq_pow_finrank
  have h2 : Fintype.card (dotBilin (K := K).orthogonal W) =
      Fintype.card K ^ Module.finrank K (dotBilin (K := K).orthogonal W) :=
    Module.card_eq_pow_finrank
  have hcard' : Fintype.card (perp q W) = Fintype.card (dotBilin (K := K).orthogonal W) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  have hpoweq : Fintype.card K ^ Module.finrank K (perp q W) =
      Fintype.card K ^ Module.finrank K (dotBilin (K := K).orthogonal W) := by
    rw [← h1, hcard', h2]
  have hfr : Module.finrank K (perp q W) =
      Module.finrank K (dotBilin (K := K).orthogonal W) :=
    Nat.pow_right_injective Fintype.one_lt_card hpoweq
  rw [hfr, LinearMap.BilinForm.finrank_orthogonal dotBilin_nondegenerate W,
    Module.finrank_fintype_fun_eq_card]
  simp

private lemma hf_sub_right {K : Type} [Field K] (q : ℕ) (u v w : Fin 6 → K) :
    hf q u (v - w) = hf q u v - hf q u w := by
  simp only [hf, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private lemma le_perp_of_isotropic {K : Type} [Field K] {q : ℕ}
    {W : Submodule K (Fin 6 → K)} (hW : IsTotallyIsotropicSU q W) : W ≤ perp q W := by
  intro x hx
  rw [mem_perp]
  intro y hy
  exact hW y hy x hx

private lemma finrank_eq_three_and_perp_eq_self {K : Type} [Field K] [Finite K] [CharP K 2]
    {q : ℕ} (hK : Nat.card K = q ^ 2) {f : ℕ} (hq : q = 2 ^ f) {lam : K}
    (hlam : ∀ μ : K, μ ^ 3 ≠ lam) {T : (Fin 6 → K) →ₗ[K] (Fin 6 → K)}
    (hT : T ^ 3 = lam • 1) {W : Submodule K (Fin 6 → K)} (hWne : W ≠ ⊥)
    (hWiso : IsTotallyIsotropicSU q W) (hstable : ∀ y ∈ W, T y ∈ W) :
    Module.finrank K W = 3 ∧ perp q W = W := by
  obtain ⟨w0, hw0W, hw0⟩ :
      ∃ w0 ∈ W, w0 ≠ 0 := by
    obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hWne)
    exact ⟨a.1, a.2, fun h => ha (Subtype.ext h)⟩
  have hleW : tline T w0 ≤ W := tline_le_of_mem hstable hw0W
  have hleperp : W ≤ perp q W := le_perp_of_isotropic hWiso
  have hge : 3 ≤ Module.finrank K W := by
    have h := Submodule.finrank_mono hleW
    rwa [tline_finrank hlam hT hw0] at h
  have hle : Module.finrank K W ≤ 3 := by
    have h := Submodule.finrank_mono hleperp
    rw [finrank_perp hK hq] at h
    omega
  have hfr : Module.finrank K W = 3 := le_antisymm hle hge
  refine ⟨hfr, (Submodule.eq_of_le_of_finrank_eq hleperp ?_).symm⟩
  rw [finrank_perp hK hq, hfr]

private lemma one_add_pow_of_sq_zero {R : Type} [Ring R] {N : R} (hN : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, mul_add, mul_one, add_mul, one_mul]
      rw [show (n • N) * N = n • (N * N) by
        rw [← Nat.cast_smul_eq_nsmul (R := R) n N, smul_mul_assoc,
          Nat.cast_smul_eq_nsmul (R := R) n (N * N)]]
      rw [hN, nsmul_zero, add_zero]
      rw [← Nat.cast_smul_eq_nsmul (R := R) (n + 1) N, Nat.cast_add, Nat.cast_one, add_smul,
        one_smul, Nat.cast_smul_eq_nsmul (R := R) n N, add_assoc]

private lemma three_dvd_sq_sub_one {q : ℕ} (h : 3 ∣ q + 1) : 3 ∣ q ^ 2 - 1 := by
  have h1 : (q + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  have h2 : q % 3 = 2 := by omega
  have h3 : q ^ 2 % 3 = 1 := by
    rw [pow_two, Nat.mul_mod, h2]
  refine ⟨q ^ 2 / 3, ?_⟩
  have := Nat.div_add_mod (q ^ 2) 3
  omega

private lemma three_dvd_card_units {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) : 3 ∣ Nat.card Kˣ := by
  rw [Nat.card_units, hK]
  exact three_dvd_sq_sub_one hq3

private lemma exists_omega {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 (three_dvd_card_units hK hq3)
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h
    rw [h] at hg
    simp at hg
  have hg3' : (g : K) ^ 3 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hg3
  have hone : (1 : K) + 1 = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [show (2 : K) = 1 + 1 by norm_num] at h2
    exact h2
  refine ⟨(g : K), hg3', ?_, ?_⟩
  · intro h
    exact hg1 (Units.ext h)
  · have hfac : ((g : K) - 1) * ((g : K) ^ 2 + (g : K) + 1) = 0 := by
      have h : (g : K) ^ 3 - 1 = 0 := by rw [hg3', sub_self]
      rwa [show (g : K) ^ 3 - 1 = ((g : K) - 1) * ((g : K) ^ 2 + (g : K) + 1) by ring] at h
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) (by intro hh; exact hg1 (Units.ext hh))
    · exact h

private lemma dvd_of_aeval_kills_tline {K : Type} [Field K]
    {T : (Fin 6 → K) →ₗ[K] (Fin 6 → K)} {lam : K}
    (hlam : ∀ μ : K, μ ^ 3 ≠ lam) (hT : T ^ 3 = lam • 1) {w0 : Fin 6 → K}
    (hw0 : w0 ≠ 0) {r : Polynomial K} (hr : Polynomial.aeval T r w0 = 0) :
    Polynomial.X ^ 3 - Polynomial.C lam ∣ r := by
  have hmonic : (Polynomial.X ^ 3 - Polynomial.C lam : Polynomial K).Monic := monic_X3subC
  have hqne : (Polynomial.X ^ 3 - Polynomial.C lam : Polynomial K) ≠ 1 := by
    intro h
    have h' := congrArg Polynomial.natDegree h
    rw [Polynomial.natDegree_X_pow_sub_C] at h'
    simp at h'
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hmonic]
  have hmod : Polynomial.aeval T (r %ₘ (Polynomial.X ^ 3 - Polynomial.C lam)) w0 = 0 := by
    have hdiv := Polynomial.modByMonic_add_div r (Polynomial.X ^ 3 - Polynomial.C lam)
    have h : Polynomial.aeval T r w0
        = Polynomial.aeval T (r %ₘ (Polynomial.X ^ 3 - Polynomial.C lam)) w0 := by
      conv_lhs => rw [← hdiv]
      rw [map_add, map_mul, aeval_X3subC hT]
      simp
    rw [← h, hr]
  have hdeg : (r %ₘ (Polynomial.X ^ 3 - Polynomial.C lam)).natDegree ≤ 2 := by
    have hlt := Polynomial.natDegree_modByMonic_lt r hmonic hqne
    rw [Polynomial.natDegree_X_pow_sub_C] at hlt
    omega
  exact aeval_eq_zero_of_natDegree_le_two hlam hT hdeg hw0 hmod

private lemma eq_smul_one_of_dvd_cube_sub_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {q : ℕ} (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) {V : Type} [AddCommGroup V]
    [Module K V] [Nontrivial V] {T : V →ₗ[K] V} {lam : K}
    (hlam : ∀ μ : K, μ ^ 3 ≠ lam) (hT : T ^ 3 = lam • 1) {p : Polynomial K}
    (hdvd : Polynomial.X ^ 3 - Polynomial.C lam ∣ p ^ 3 - 1) :
    ∃ c : K, c ^ 3 = 1 ∧ Polynomial.aeval T p = c • 1 := by
  have hfac : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by ring
  rw [hfac] at hdvd
  by_cases h1 : Polynomial.X ^ 3 - Polynomial.C lam ∣ p - 1
  · have h0 : Polynomial.aeval T (p - 1) = 0 :=
      (aeval_eq_zero_iff_dvd hlam hT (p - 1)).mpr h1
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact ⟨1, one_pow 3, by rw [h0, one_smul]⟩
  · have h2 : Polynomial.X ^ 3 - Polynomial.C lam ∣ p ^ 2 + p + 1 := by
      have hcop : IsCoprime (Polynomial.X ^ 3 - Polynomial.C lam) (p - 1) :=
        (X3subC_irreducible hlam).coprime_iff_not_dvd.mpr h1
      exact hcop.dvd_of_dvd_mul_left hdvd
    obtain ⟨ω, hω3, hωne, hωsum⟩ := exists_omega hK hq3
    have hμ : (Polynomial.aeval T p) ^ 2 + Polynomial.aeval T p + 1 = 0 := by
      have h0 : Polynomial.aeval T (p ^ 2 + p + 1) = 0 :=
        (aeval_eq_zero_iff_dvd hlam hT (p ^ 2 + p + 1)).mpr h2
      simpa only [map_add, map_pow, map_one] using h0
    have hsum1 : ω + ω ^ 2 = 1 := by
      have hone : (1 : K) + 1 = 0 := by
        have h2c : (2 : K) = 0 := CharP.cast_eq_zero K 2
        rw [show (2 : K) = 1 + 1 by norm_num] at h2c
        exact h2c
      have hh : ω ^ 2 + ω + 1 = 1 + 1 := by rw [hωsum, hone]
      have h2' : ω ^ 2 + ω = 1 := add_right_cancel hh
      rwa [add_comm] at h2'
    have hωω : ω * ω ^ 2 = 1 := by
      rw [show ω * ω ^ 2 = ω ^ 3 by ring, hω3]
    have hprod : (Polynomial.aeval T p - ω • 1) * (Polynomial.aeval T p - ω ^ 2 • 1) = 0 := by
      have hexp : (Polynomial.aeval T p - ω • 1) * (Polynomial.aeval T p - ω ^ 2 • 1)
          = (Polynomial.aeval T p) ^ 2 - (ω + ω ^ 2) • Polynomial.aeval T p
              + (ω * ω ^ 2) • (1 : V →ₗ[K] V) := by
        simp only [sub_mul, mul_sub, mul_sub, pow_two, smul_mul_assoc, mul_smul_comm,
          smul_smul, one_mul, mul_one]
        module
      rw [hexp, hsum1, hωω]
      simp only [one_smul]
      have hμμ : Polynomial.aeval T p + Polynomial.aeval T p = 0 := by
        have h2 : (2 : ℕ) • Polynomial.aeval T p = 0 := by
          rw [← Nat.cast_smul_eq_nsmul (R := K) 2 (Polynomial.aeval T p),
            CharP.cast_eq_zero K 2, zero_smul]
        simpa only [two_smul] using h2
      rw [sub_eq_add_neg, show -(Polynomial.aeval T p) = Polynomial.aeval T p by
        rw [neg_eq_iff_add_eq_zero]; exact hμμ]
      exact hμ
    have hpq : Polynomial.aeval T ((p - Polynomial.C ω) * (p - Polynomial.C (ω ^ 2))) = 0 := by
      rw [map_mul]
      have e1 : Polynomial.aeval T (p - Polynomial.C ω) = Polynomial.aeval T p - ω • 1 := by
        rw [map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one']
      have e2 : Polynomial.aeval T (p - Polynomial.C (ω ^ 2))
          = Polynomial.aeval T p - ω ^ 2 • 1 := by
        rw [map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one']
      rw [e1, e2]
      exact hprod
    have hdvd2 : Polynomial.X ^ 3 - Polynomial.C lam
        ∣ (p - Polynomial.C ω) * (p - Polynomial.C (ω ^ 2)) :=
      (aeval_eq_zero_iff_dvd hlam hT _).mp hpq
    by_cases hω : Polynomial.X ^ 3 - Polynomial.C lam ∣ p - Polynomial.C ω
    · have h0 : Polynomial.aeval T (p - Polynomial.C ω) = 0 :=
        (aeval_eq_zero_iff_dvd hlam hT (p - Polynomial.C ω)).mpr hω
      rw [map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one', sub_eq_zero] at h0
      exact ⟨ω, hω3, h0⟩
    · have hcop : IsCoprime (Polynomial.X ^ 3 - Polynomial.C lam) (p - Polynomial.C ω) :=
        (X3subC_irreducible hlam).coprime_iff_not_dvd.mpr hω
      have hdvd3 : Polynomial.X ^ 3 - Polynomial.C lam ∣ p - Polynomial.C (ω ^ 2) :=
        hcop.dvd_of_dvd_mul_left hdvd2
      have h0 : Polynomial.aeval T (p - Polynomial.C (ω ^ 2)) = 0 :=
        (aeval_eq_zero_iff_dvd hlam hT (p - Polynomial.C (ω ^ 2))).mpr hdvd3
      rw [map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one', sub_eq_zero] at h0
      refine ⟨ω ^ 2, ?_, h0⟩
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]

private lemma aeval_mul_T {K : Type} [Field K] {T : (Fin 6 → K) →ₗ[K] (Fin 6 → K)}
    (p : Polynomial K) : Polynomial.aeval T p * T = T * Polynomial.aeval T p := by
  have hX : Polynomial.aeval T (Polynomial.X : Polynomial K) = T := Polynomial.aeval_X T
  calc Polynomial.aeval T p * T
      = Polynomial.aeval T p * Polynomial.aeval T Polynomial.X := by rw [hX]
    _ = Polynomial.aeval T (p * Polynomial.X) := by rw [map_mul]
    _ = Polynomial.aeval T (Polynomial.X * p) := by rw [mul_comm]
    _ = Polynomial.aeval T Polynomial.X * Polynomial.aeval T p := by rw [map_mul]
    _ = T * Polynomial.aeval T p := by rw [hX]

private lemma smul_pow_end {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (c : K) (x : V →ₗ[K] V) (n : ℕ) : (c • x) ^ n = c ^ n • x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, smul_mul_smul_comm, pow_succ, pow_succ]

private lemma is_scalar_of_cube_eq_one {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) {lam : K}
    (hlam : ∀ μ : K, μ ^ 3 ≠ lam) {T : (Fin 6 → K) →ₗ[K] (Fin 6 → K)}
    (hT : T ^ 3 = lam • 1) {W : Submodule K (Fin 6 → K)} (hWperp : perp q W = W)
    {w0 : Fin 6 → K} (hw0 : w0 ∈ W) (hw0ne : w0 ≠ 0) (hspan : W = tline T w0)
    {M : GL (Fin 6) K} (hMiso : IsHermIsometry q (M : Matrix (Fin 6) (Fin 6) K))
    (hMT : Matrix.toLin' (M : Matrix (Fin 6) (Fin 6) K) * T
      = T * Matrix.toLin' (M : Matrix (Fin 6) (Fin 6) K))
    (hMW : ∀ w ∈ W, (M : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W)
    (hM3 : (M : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1) :
    ∃ c : K, c ^ 3 = 1 ∧ (M : Matrix (Fin 6) (Fin 6) K) = c • 1 := by
  set MtoLin : (Fin 6 → K) →ₗ[K] (Fin 6 → K) := Matrix.toLin' (M : Matrix (Fin 6) (Fin 6) K)
    with hMtoLin
  have hMtoLin_apply : ∀ v : Fin 6 → K, MtoLin v = (M : Matrix (Fin 6) (Fin 6) K) *ᵥ v := by
    intro v
    rw [hMtoLin, Matrix.toLin'_apply]
  have hMtoLin3 : MtoLin ^ 3 = 1 := by
    rw [hMtoLin, ← Matrix.toLin'_pow, hM3, Matrix.toLin'_one]
    exact Module.End.one_eq_id.symm
  have hMisoL : ∀ u v : Fin 6 → K, hf q (MtoLin u) (MtoLin v) = hf q u v := by
    intro u v
    rw [hMtoLin_apply u, hMtoLin_apply v]
    exact hMiso u v
  have hMWl : ∀ y ∈ W, MtoLin y ∈ W := by
    intro y hy
    rw [hMtoLin_apply y]
    exact hMW y hy
  have hMw0t : MtoLin w0 ∈ tline T w0 := by
    rw [← hspan]
    exact hMWl w0 hw0
  obtain ⟨u0, u1, u2, hpw0⟩ := (mem_tline_iff (T := T) w0 (MtoLin w0)).mp hMw0t
  let p : Polynomial K := Polynomial.C u0 + Polynomial.C u1 * Polynomial.X
    + Polynomial.C u2 * Polynomial.X ^ 2
  have hpval : Polynomial.aeval T p w0 = u0 • w0 + u1 • T w0 + u2 • (T ^ 2) w0 := by
    dsimp only [p]
    rw [aeval_quad_general]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hST : (MtoLin - Polynomial.aeval T p) * T = T * (MtoLin - Polynomial.aeval T p) := by
    rw [sub_mul, mul_sub, hMT, aeval_mul_T]
  have hSw0 : (MtoLin - Polynomial.aeval T p) w0 = 0 := by
    rw [LinearMap.sub_apply, hpw0, hpval, sub_self]
  have hkey : ∀ x ∈ W, MtoLin x = Polynomial.aeval T p x := by
    intro x hx
    have hx' : x ∈ tline T w0 := by rw [← hspan]; exact hx
    have h0 := apply_eq_zero_on_tline hST hSw0 x hx'
    rwa [LinearMap.sub_apply, sub_eq_zero] at h0
  have hPn : ∀ n : ℕ, ((Polynomial.aeval T p) ^ n) w0 = (MtoLin ^ n) w0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hmem : (MtoLin ^ n) w0 ∈ W :=
          pow_mem_of_stable (T := MtoLin) (S := W) hMWl n hw0
        calc ((Polynomial.aeval T p) ^ (n + 1)) w0
            = (Polynomial.aeval T p) (((Polynomial.aeval T p) ^ n) w0) := by
              rw [pow_succ', Module.End.mul_apply]
          _ = (Polynomial.aeval T p) ((MtoLin ^ n) w0) := by rw [ih]
          _ = MtoLin ((MtoLin ^ n) w0) := (hkey _ hmem).symm
          _ = (MtoLin ^ (n + 1)) w0 := by rw [pow_succ', Module.End.mul_apply]
  have hP3 : ((Polynomial.aeval T p) ^ 3) w0 = w0 := by
    rw [hPn 3, hMtoLin3, Module.End.one_apply]
  have hkill : Polynomial.aeval T (p ^ 3 - 1) w0 = 0 := by
    rw [map_sub, map_pow, map_one, LinearMap.sub_apply, hP3, Module.End.one_apply, sub_self]
  have hdvd : Polynomial.X ^ 3 - Polynomial.C lam ∣ p ^ 3 - 1 :=
    dvd_of_aeval_kills_tline hlam hT hw0ne hkill
  obtain ⟨c, hc3, hc⟩ := eq_smul_one_of_dvd_cube_sub_one hK hq3 hlam hT hdvd
  have hMwc : ∀ w ∈ W, MtoLin w = c • w := by
    intro w hw
    rw [hkey w hw, hc, LinearMap.smul_apply, Module.End.one_apply]
  have hc0 : c ≠ 0 := by
    intro h0
    have h : (0 : K) = 1 := by simpa [h0] using hc3
    exact (zero_ne_one : (0 : K) ≠ 1) h
  have hcqp : c ^ (q + 1) = 1 := by
    obtain ⟨k, hk⟩ := hq3
    rw [hk, pow_mul, hc3, one_pow]
  have hcq : c ^ q = c⁻¹ := by
    rw [pow_succ'] at hcqp
    exact eq_inv_of_mul_eq_one_right hcqp
  have hinvq : (c⁻¹) ^ q = c := by rw [inv_pow, hcq, inv_inv]
  have hNV : ∀ v : Fin 6 → K, (MtoLin - c • 1) v ∈ W := by
    intro v
    rw [← hWperp, mem_perp]
    intro w hw
    have h1 : MtoLin (c⁻¹ • w) = w := by
      rw [map_smul, hMwc w hw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hiso := hMisoL (c⁻¹ • w) v
    rw [h1, hf_smul_left, hinvq] at hiso
    rw [LinearMap.sub_apply, hf_sub_right, LinearMap.smul_apply, Module.End.one_apply,
      hf_smul_right, hiso, sub_self]
  set N : (Fin 6 → K) →ₗ[K] (Fin 6 → K) := MtoLin - c • 1 with hNdef
  have hNV' : ∀ v : Fin 6 → K, N v ∈ W := by
    intro v; rw [hNdef]; exact hNV v
  have hNfix : ∀ w ∈ W, N w = 0 := by
    intro w hw
    rw [hNdef, LinearMap.sub_apply, hMwc w hw, LinearMap.smul_apply, Module.End.one_apply,
      sub_self]
  have hNN : N * N = 0 := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, LinearMap.zero_apply]
    exact hNfix (N v) (hNV' v)
  have hMtoLin_eq : MtoLin = c • 1 := by
    set N' : (Fin 6 → K) →ₗ[K] (Fin 6 → K) := c⁻¹ • N with hN'def
    have hN'2 : N' * N' = 0 := by
      rw [hN'def, smul_mul_smul_comm, hNN, smul_zero]
    have hM'' : c⁻¹ • MtoLin = 1 + N' := by
      rw [hN'def, hNdef, smul_sub, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      abel
    have hM'3 : (c⁻¹ • MtoLin) ^ 3 = 1 := by
      rw [smul_pow_end, hMtoLin3,
        show (c⁻¹ : K) ^ 3 = 1 by rw [inv_pow, hc3, inv_one], one_smul]
    have hpow3 : (1 + N') ^ 3 = 1 + N' := by
      have h3 : (3 : ℕ) • N' = N' := by
        have h2 : (2 : ℕ) • N' = 0 := by
          rw [← Nat.cast_smul_eq_nsmul (R := K) 2 N', CharP.cast_eq_zero K 2, zero_smul]
        rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, h2, zero_add, one_nsmul]
      rw [one_add_pow_of_sq_zero hN'2 3, h3]
    have hN'0 : N' = 0 := by
      have h1 : (1 : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) + N' = 1 := by
        have h := hM'3
        rw [hM''] at h
        rwa [hpow3] at h
      exact add_left_cancel (show (1 : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) + N' = 1 + 0 by
        rw [h1, add_zero])
    have hN0 : N = 0 := by
      rw [hN'def, smul_eq_zero] at hN'0
      rcases hN'0 with h | h
      · exact absurd h (inv_ne_zero hc0)
      · exact h
    rw [hNdef, sub_eq_zero] at hN0
    exact hN0
  refine ⟨c, hc3, ?_⟩
  rw [Matrix.ext_iff_mulVec]
  intro v
  have h := congrArg (fun f : (Fin 6 → K) →ₗ[K] (Fin 6 → K) => f v) hMtoLin_eq
  rw [hMtoLin, Matrix.toLin'_apply, LinearMap.smul_apply, Module.End.one_apply] at h
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  exact h
private lemma exists_two_pow_of_card {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) : ∃ f : ℕ, q = 2 ^ f := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hn, hcard⟩ := FiniteField.card (K := K) 2
  have hcard' : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hq2 : q ^ 2 = 2 ^ (n : ℕ) := by rw [← hK, hcard']
  have hdvd : q ∣ 2 ^ (n : ℕ) := ⟨q, by rw [← pow_two, hq2]⟩
  obtain ⟨f, _, hf⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨f, hf⟩

private lemma central_mul_assoc {G : Type*} [Group G] {w : G}
    (hw : ∀ x : G, w * x = x * w) (x y : G) : x * (w * y) = w * (x * y) :=
  calc x * (w * y) = (x * w) * y := (mul_assoc x w y).symm
    _ = (w * x) * y := by rw [← hw x]
    _ = w * (x * y) := mul_assoc w x y

private lemma pow_mul_right_of_central {G : Type*} [Group G] {z a b : G}
    (hz : ∀ n : ℕ, ∀ x : G, z ^ n * x = x * z ^ n)
    (hab : a * b = z * b * a) :
    ∀ n : ℕ, a ^ n * b = z ^ n * b * a ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc a ^ (n + 1) * b
          = a * (a ^ n * b) := by rw [pow_succ', mul_assoc]
        _ = a * (z ^ n * b * a ^ n) := by rw [ih]
        _ = z ^ n * (a * (b * a ^ n)) := by
              rw [mul_assoc (z ^ n) b (a ^ n)]
              exact central_mul_assoc (hz n) a (b * a ^ n)
        _ = z ^ n * ((a * b) * a ^ n) := by rw [mul_assoc]
        _ = z ^ n * ((z * b * a) * a ^ n) := by rw [hab]
        _ = z ^ (n + 1) * b * a ^ (n + 1) := by rw [pow_succ]; group

private lemma mul_cube_eq_cube_mul_cube {G : Type*} [Group G]
    (hcomm : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G)
    (hcube : ∀ a : G, a ^ 3 ∈ Subgroup.center G) :
    ∀ a b : G, (a * b) ^ 3 = a ^ 3 * b ^ 3 := by
  intro a b
  set z : G := a * b * a⁻¹ * b⁻¹ with hzdef
  have hzmem : z ∈ Subgroup.center G := by rw [hzdef]; exact hcomm a b
  have hzpow : ∀ n : ℕ, ∀ x : G, z ^ n * x = x * z ^ n :=
    fun n x => (Subgroup.mem_center_iff.mp (pow_mem hzmem n) x).symm
  have hzneg : ∀ x : G, z⁻¹ * x = x * z⁻¹ :=
    fun x => (Subgroup.mem_center_iff.mp (inv_mem hzmem) x).symm
  have hznegpow : ∀ n : ℕ, ∀ x : G, (z⁻¹) ^ n * x = x * (z⁻¹) ^ n :=
    fun n x => (Subgroup.mem_center_iff.mp (pow_mem (inv_mem hzmem) n) x).symm
  have hab : a * b = z * b * a := by rw [hzdef]; group
  have hba : b * a = z⁻¹ * (a * b) := by rw [hzdef]; group
  have hclaim1 : ∀ n : ℕ, a ^ n * b = z ^ n * b * a ^ n :=
    pow_mul_right_of_central hzpow hab
  have hba_rel : b * a = z⁻¹ * a * b := by rw [hba, mul_assoc]
  have hclaim2 : ∀ n : ℕ, b ^ n * a = (z⁻¹) ^ n * a * b ^ n :=
    pow_mul_right_of_central hznegpow hba_rel
  have hz3 : z ^ 3 = 1 := by
    have h := hclaim1 3
    have ha3c : a ^ 3 * b = b * a ^ 3 :=
      (Subgroup.mem_center_iff.mp (hcube a) b).symm
    rw [ha3c] at h
    have h' : b * a ^ 3 = z ^ 3 * (b * a ^ 3) := by
      nth_rewrite 1 [h]
      rw [mul_assoc]
    have h1 : (1 : G) = z ^ 3 :=
      mul_right_cancel (show (1 : G) * (b * a ^ 3) = z ^ 3 * (b * a ^ 3) by
        rw [one_mul]; exact h')
    exact h1.symm
  have hba2 : b ^ 2 * a = (z⁻¹) ^ 2 * a * b ^ 2 := hclaim2 2
  have hzicom : Commute z⁻¹ (a * b) := hzneg (a * b)
  have hmul : (b * a) ^ 2 = (z⁻¹) ^ 2 * (a * b) ^ 2 := by
    rw [hba]
    exact hzicom.mul_pow 2
  have hkey : a * (a * b) ^ 2 * b = z⁻¹ * a ^ 3 * b ^ 3 := by
    calc a * (a * b) ^ 2 * b = a ^ 2 * (b * a) * b ^ 2 := by
          simp only [pow_two, mul_assoc]
      _ = a ^ 2 * (z⁻¹ * (a * b)) * b ^ 2 := by rw [hba]
      _ = z⁻¹ * (a ^ 2 * (a * b)) * b ^ 2 := by
            congr 1
            exact central_mul_assoc hzneg (a ^ 2) (a * b)
      _ = z⁻¹ * a ^ 3 * b ^ 3 := by group
  calc (a * b) ^ 3 = a * (b * a) ^ 2 * b := by
        simp only [pow_succ, pow_two, pow_zero, one_mul, mul_assoc]
    _ = a * ((z⁻¹) ^ 2 * (a * b) ^ 2) * b := by rw [hmul]
    _ = (z⁻¹) ^ 2 * (a * (a * b) ^ 2 * b) := by
          rw [show a * ((z⁻¹) ^ 2 * (a * b) ^ 2) * b
                = (z⁻¹) ^ 2 * (a * (a * b) ^ 2 * b) by
                rw [central_mul_assoc (hznegpow 2) a ((a * b) ^ 2)]; group]
    _ = (z⁻¹) ^ 2 * (z⁻¹ * a ^ 3 * b ^ 3) := by rw [hkey]
    _ = a ^ 3 * b ^ 3 := by
          have h1 : (z⁻¹) ^ 2 * (z⁻¹ * a ^ 3 * b ^ 3)
              = (z⁻¹) ^ 3 * (a ^ 3 * b ^ 3) := by group
          have h2 : (z⁻¹) ^ 3 = 1 := by rw [inv_pow, hz3, inv_one]
          rw [h1, h2, one_mul]

private lemma scalarGL_injective {K : Type*} [Field K] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K) := by
  intro c c' h
  have h' : (Matrix.GeneralLinearGroup.scalar (Fin 6) c : Matrix (Fin 6) (Fin 6) K)
      = (Matrix.GeneralLinearGroup.scalar (Fin 6) c' : Matrix (Fin 6) (Fin 6) K) :=
    congrArg (fun x : GL (Fin 6) K => (x : Matrix (Fin 6) (Fin 6) K)) h
  have h00 := congrFun (congrFun h' 0) 0
  exact Units.ext (by simpa using h00)

theorem u6_par_impossible {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1)
    (Ahat : Subgroup (GL (Fin 6) K))
    (hiso : ∀ a ∈ Ahat, IsHermIsometry q (a : Matrix (Fin 6) (Fin 6) K))
    (hZ : ∀ c : Kˣ, c ^ (q + 1) = 1 → Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ Ahat)
    (hcomm : ∀ a ∈ Ahat, ∀ b ∈ Ahat, ∃ c : Kˣ, c ^ (q + 1) = 1 ∧
      a * b * a⁻¹ * b⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (hcube : ∀ a ∈ Ahat, ∃ c : Kˣ, c ^ (q + 1) = 1 ∧
      a ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    (hcard : 3 ^ 3 * (q + 1) ≤ Nat.card Ahat)
    (d : GL (Fin 6) K) (hdA : d ∈ Ahat) (lam : K)
    (hd3 : (d : Matrix (Fin 6) (Fin 6) K) ^ 3 = lam • (1 : Matrix (Fin 6) (Fin 6) K))
    (hlam : ∀ μ : K, μ ^ 3 ≠ lam)
    (hker : ∀ a ∈ Ahat, (∀ g : GL (Fin 6) K, IsHermIsometry q (g : Matrix (Fin 6) (Fin 6) K) →
        g * d = d * g → a * g = g * a) →
      ∃ (k : ℤ) (c : Kˣ), c ^ (q + 1) = 1 ∧
        a = d ^ k * Matrix.GeneralLinearGroup.scalar (Fin 6) c) :
    ¬ ∃ W : Submodule K (Fin 6 → K), W ≠ ⊥ ∧ IsTotallyIsotropicSU q W ∧
      ∀ a ∈ Ahat, ∀ w ∈ W, (a : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W := by
  rintro ⟨W, hWne, hWiso, hWstab⟩
  obtain ⟨f, hf⟩ := exists_two_pow_of_card hK
  set T : (Fin 6 → K) →ₗ[K] (Fin 6 → K) := Matrix.toLin' (d : Matrix (Fin 6) (Fin 6) K)
    with hTdef
  have hT3 : T ^ 3 = lam • 1 := by
    rw [hTdef, ← Matrix.toLin'_pow, hd3]
    ext v
    simp [Matrix.toLin'_apply, Matrix.smul_mulVec]
  have hdW : ∀ w ∈ W, T w ∈ W := by
    intro w hw
    rw [hTdef, Matrix.toLin'_apply]
    exact hWstab d hdA w hw
  obtain ⟨hWfr, hWperp⟩ :=
    finrank_eq_three_and_perp_eq_self hK hf hlam hT3 hWne hWiso hdW
  obtain ⟨w0, hw0W, hw0ne⟩ : ∃ w0 ∈ W, w0 ≠ 0 := by
    obtain ⟨x, hx⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hWne)
    exact ⟨x.1, x.2, fun h => hx (Subtype.ext h)⟩
  have hle : tline T w0 ≤ W := tline_le_of_mem hdW hw0W
  have hfr : Module.finrank K (tline T w0) = 3 := tline_finrank hlam hT3 hw0ne
  have hspan : W = tline T w0 :=
    (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hWfr])).symm
  let sc : Kˣ →* GL (Fin 6) K := Matrix.GeneralLinearGroup.scalar (Fin 6)
  let dA : Ahat := ⟨d, hdA⟩
  have hsc_center : ∀ c : Kˣ, sc c ∈ Subgroup.center (GL (Fin 6) K) := by
    intro c
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcomm_gl : ∀ a ∈ Ahat, ∃ c : Kˣ,
      (a : GL (Fin 6) K) * d * (a : GL (Fin 6) K)⁻¹ * d⁻¹ = sc c := by
    intro a ha
    obtain ⟨c, hc, hcab⟩ := hcomm a ha d hdA
    exact ⟨c, hcab⟩
  let chi : Ahat →* GL (Fin 6) K := MonoidHom.mk'
    (fun a => (a : GL (Fin 6) K) * d * (a : GL (Fin 6) K)⁻¹ * d⁻¹) (by
      intro a b
      obtain ⟨c, hc⟩ := hcomm_gl (b : GL (Fin 6) K) b.2
      have hcent : ∀ x : GL (Fin 6) K, x * sc c = sc c * x :=
        fun x => (Subgroup.mem_center_iff.mp (hsc_center c)) x
      change (a : GL (Fin 6) K) * (b : GL (Fin 6) K) * d *
              ((b : GL (Fin 6) K)⁻¹ * (a : GL (Fin 6) K)⁻¹) * d⁻¹
          = (a : GL (Fin 6) K) * d * (a : GL (Fin 6) K)⁻¹ * d⁻¹ *
              ((b : GL (Fin 6) K) * d * (b : GL (Fin 6) K)⁻¹ * d⁻¹)
      calc (a : GL (Fin 6) K) * (b : GL (Fin 6) K) * d *
              ((b : GL (Fin 6) K)⁻¹ * (a : GL (Fin 6) K)⁻¹) * d⁻¹
          = (a : GL (Fin 6) K) * ((b : GL (Fin 6) K) * d * (b : GL (Fin 6) K)⁻¹ * d⁻¹) *
              d * (a : GL (Fin 6) K)⁻¹ * d⁻¹ := by group
        _ = (a : GL (Fin 6) K) * sc c * d * (a : GL (Fin 6) K)⁻¹ * d⁻¹ := by rw [hc]
        _ = sc c * ((a : GL (Fin 6) K) * d * (a : GL (Fin 6) K)⁻¹ * d⁻¹) := by
              rw [hcent (a : GL (Fin 6) K)]; group
        _ = (a : GL (Fin 6) K) * d * (a : GL (Fin 6) K)⁻¹ * d⁻¹ * sc c := by
              rw [(hcent _).symm]
        _ = (a : GL (Fin 6) K) * d * (a : GL (Fin 6) K)⁻¹ * d⁻¹ *
              ((b : GL (Fin 6) K) * d * (b : GL (Fin 6) K)⁻¹ * d⁻¹) := by rw [hc])
  have hcommA : ∀ a b : Ahat, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center Ahat := by
    intro a b
    obtain ⟨c, hc, hcab⟩ := hcomm (a : Ahat) a.2 (b : Ahat) b.2
    have hmem : (⟨sc c, hZ c hc⟩ : Ahat) ∈ Subgroup.center Ahat :=
      Subgroup.mem_center_iff.mpr (fun x => by
        apply Subtype.ext
        show (x : GL (Fin 6) K) * sc c = sc c * (x : GL (Fin 6) K)
        exact Subgroup.mem_center_iff.mp (hsc_center c) (x : GL (Fin 6) K))
    have heq : a * b * a⁻¹ * b⁻¹ = (⟨sc c, hZ c hc⟩ : Ahat) := by
      apply Subtype.ext
      show (a : GL (Fin 6) K) * (b : GL (Fin 6) K) * (a : GL (Fin 6) K)⁻¹
          * (b : GL (Fin 6) K)⁻¹ = sc c
      exact hcab
    rwa [heq]
  have hcubeA : ∀ a : Ahat, a ^ 3 ∈ Subgroup.center Ahat := by
    intro a
    obtain ⟨c, hc, hcab⟩ := hcube (a : Ahat) a.2
    have hmem : (⟨sc c, hZ c hc⟩ : Ahat) ∈ Subgroup.center Ahat :=
      Subgroup.mem_center_iff.mpr (fun x => by
        apply Subtype.ext
        show (x : GL (Fin 6) K) * sc c = sc c * (x : GL (Fin 6) K)
        exact Subgroup.mem_center_iff.mp (hsc_center c) (x : GL (Fin 6) K))
    have heq : a ^ 3 = (⟨sc c, hZ c hc⟩ : Ahat) := by
      apply Subtype.ext
      show (a : GL (Fin 6) K) ^ 3 = sc c
      exact hcab
    rwa [heq]
  let Cg : Subgroup Ahat := chi.ker
  let psi : Cg →* GL (Fin 6) K := MonoidHom.mk'
    (fun a => (((a : Cg) : Ahat) : GL (Fin 6) K) ^ 3) (by
      intro a b
      have h := mul_cube_eq_cube_mul_cube hcommA hcubeA ((a : Cg) : Ahat) ((b : Cg) : Ahat)
      simpa using congrArg (fun x : Ahat => (x : GL (Fin 6) K)) h)
  have hchi_range_le : chi.range ≤ (rootsOfUnity 3 K).map sc := by
    rintro x ⟨a, rfl⟩
    obtain ⟨c, hcab⟩ := hcomm_gl (a : Ahat) a.2
    have hchi3 : (chi a) ^ 3 = 1 := by
      obtain ⟨c', hc', hc'ab⟩ := hcube (a : Ahat) a.2
      have hmem : sc c' ∈ Ahat := hZ c' hc'
      have ha3 : a ^ 3 = (⟨sc c', hmem⟩ : Ahat) := Subtype.ext hc'ab
      have hsc1 : chi (⟨sc c', hmem⟩ : Ahat) = 1 := by
        change (sc c' : GL (Fin 6) K) * d * (sc c')⁻¹ * d⁻¹ = 1
        have hcent2 : (sc c' : GL (Fin 6) K) * d = d * sc c' :=
          (Subgroup.mem_center_iff.mp (hsc_center c') d).symm
        rw [hcent2]
        group
      rw [show (chi a) ^ 3 = chi (a ^ 3) by rw [map_pow], ha3, hsc1]
    have hc3 : c ^ 3 = 1 := by
      apply (show Function.Injective sc from scalarGL_injective)
      rw [map_pow, map_one, ← hcab]
      exact hchi3
    change (a : GL (Fin 6) K) * d * (a : GL (Fin 6) K)⁻¹ * d⁻¹
      ∈ (rootsOfUnity 3 K).map sc
    rw [hcab]
    exact (Subgroup.mem_map_iff_mem (show Function.Injective sc from
      scalarGL_injective)).mpr ((mem_rootsOfUnity 3 c).mpr hc3)
  have hpsi_range_le : psi.range ≤ (rootsOfUnity (q + 1) K).map sc := by
    rintro x ⟨a, rfl⟩
    obtain ⟨c, hc, hcab⟩ := hcube ((a : Cg) : Ahat) ((a : Cg) : Ahat).2
    change (((a : Cg) : Ahat) : GL (Fin 6) K) ^ 3 ∈ (rootsOfUnity (q + 1) K).map sc
    rw [hcab]
    exact (Subgroup.mem_map_iff_mem (show Function.Injective sc from
      scalarGL_injective)).mpr ((mem_rootsOfUnity (q + 1) c).mpr hc)
  have hex : ∀ a : psi.ker, ∃ c : K, c ^ 3 = 1 ∧
      ((((a : Cg) : Ahat) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = c • (1 : Matrix (Fin 6) (Fin 6) K) := by
    intro a
    have hchi1 : chi (a : Cg) = 1 := MonoidHom.mem_ker.mp (a : Cg).2
    have hcomm_d : ((a : Cg) : GL (Fin 6) K) * d = d * ((a : Cg) : GL (Fin 6) K) := by
      have h := hchi1
      change ((a : Cg) : GL (Fin 6) K) * d * (((a : Cg) : GL (Fin 6) K))⁻¹ * d⁻¹ = 1 at h
      calc ((a : Cg) : GL (Fin 6) K) * d
          = ((a : Cg) : GL (Fin 6) K) * d * (((a : Cg) : GL (Fin 6) K))⁻¹ * d⁻¹ * d
              * ((a : Cg) : GL (Fin 6) K) := by group
        _ = 1 * d * ((a : Cg) : GL (Fin 6) K) := by rw [h]
        _ = d * ((a : Cg) : GL (Fin 6) K) := by group
    have hmat : ((((a : Cg) : Ahat) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
          * (d : Matrix (Fin 6) (Fin 6) K)
        = (d : Matrix (Fin 6) (Fin 6) K)
          * ((((a : Cg) : Ahat) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
      congrArg (fun x : GL (Fin 6) K => (x : Matrix (Fin 6) (Fin 6) K)) hcomm_d
    have hMT : Matrix.toLin' ((((a : Cg) : Ahat) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * T
        = T * Matrix.toLin' ((((a : Cg) : Ahat) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      rw [hTdef]
      change Matrix.toLin' ((((a : Cg) : Ahat) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
            ∘ₗ Matrix.toLin' (d : Matrix (Fin 6) (Fin 6) K)
          = Matrix.toLin' (d : Matrix (Fin 6) (Fin 6) K)
            ∘ₗ Matrix.toLin' ((((a : Cg) : Ahat) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
      rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
      exact congrArg Matrix.toLin' hmat
    have hMW : ∀ w ∈ W, ((((a : Cg) : Ahat) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ w ∈ W :=
      hWstab ((a : Cg) : Ahat) ((a : Cg) : Ahat).2
    have hM3 : ((((a : Cg) : Ahat) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) ^ 3 = 1 := by
      have h : ((((a : Cg) : Ahat) : GL (Fin 6) K)) ^ 3 = 1 := MonoidHom.mem_ker.mp a.2
      have h' := congrArg (fun x : GL (Fin 6) K => (x : Matrix (Fin 6) (Fin 6) K)) h
      simpa using h'
    exact is_scalar_of_cube_eq_one hK hq3 hlam hT3 hWperp hw0W hw0ne hspan
      (hiso ((a : Cg) : Ahat) ((a : Cg) : Ahat).2) hMT hMW hM3
  have hker_le : Nat.card psi.ker ≤ 3 := by
    haveI : NeZero 3 := ⟨by norm_num⟩
    let f : psi.ker → rootsOfUnity 3 K := fun a =>
      rootsOfUnity.mkOfPowEq (Classical.choose (hex a)) (Classical.choose_spec (hex a)).1
    have hf_inj : Function.Injective f := by
      intro a b hab
      have hc : Classical.choose (hex a) = Classical.choose (hex b) := by
        have h := congrArg (fun u : rootsOfUnity 3 K => ((u : Kˣ) : K)) hab
        rwa [rootsOfUnity.val_mkOfPowEq_coe, rootsOfUnity.val_mkOfPowEq_coe] at h
      have hMa := (Classical.choose_spec (hex a)).2
      have hMb := (Classical.choose_spec (hex b)).2
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      rw [hMa, hMb, hc]
    calc Nat.card psi.ker ≤ Nat.card (rootsOfUnity 3 K) :=
          Nat.card_le_card_of_injective f hf_inj
      _ ≤ 3 := card_rootsOfUnity K 3
  have hA_le : Nat.card Ahat ≤ 3 * Nat.card Cg := by
    have hcardq : Nat.card Ahat = Nat.card (Ahat ⧸ Cg) * Nat.card Cg :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Cg
    have hiso : Ahat ⧸ Cg ≃* chi.range := by
      change Ahat ⧸ chi.ker ≃* chi.range
      exact QuotientGroup.quotientKerEquivRange chi
    have h1 : Nat.card (Ahat ⧸ Cg) = Nat.card chi.range := Nat.card_congr hiso.toEquiv
    have h2 : Nat.card chi.range ≤ 3 := by
      calc Nat.card chi.range ≤ Nat.card ((rootsOfUnity 3 K).map sc) :=
            Subgroup.card_le_of_le hchi_range_le
        _ = Nat.card (rootsOfUnity 3 K) :=
            Subgroup.card_map_of_injective (show Function.Injective sc from
              scalarGL_injective)
        _ ≤ 3 := card_rootsOfUnity K 3
    rw [hcardq, h1]
    exact Nat.mul_le_mul_right (Nat.card Cg) h2
  have hCg_le : Nat.card Cg ≤ 3 * (q + 1) := by
    have hcardq : Nat.card Cg = Nat.card (Cg ⧸ psi.ker) * Nat.card psi.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup psi.ker
    have hiso : Cg ⧸ psi.ker ≃* psi.range := QuotientGroup.quotientKerEquivRange psi
    have h1 : Nat.card (Cg ⧸ psi.ker) = Nat.card psi.range := Nat.card_congr hiso.toEquiv
    have h2 : Nat.card psi.range ≤ q + 1 := by
      haveI : NeZero (q + 1) := ⟨Nat.succ_ne_zero q⟩
      calc Nat.card psi.range ≤ Nat.card ((rootsOfUnity (q + 1) K).map sc) :=
            Subgroup.card_le_of_le hpsi_range_le
        _ = Nat.card (rootsOfUnity (q + 1) K) :=
            Subgroup.card_map_of_injective (show Function.Injective sc from
              scalarGL_injective)
        _ ≤ q + 1 := card_rootsOfUnity K (q + 1)
    rw [hcardq, h1]
    calc Nat.card psi.range * Nat.card psi.ker ≤ (q + 1) * 3 := Nat.mul_le_mul h2 hker_le
      _ = 3 * (q + 1) := by ring
  have h1 : 27 * (q + 1) ≤ 9 * (q + 1) := by
    calc 27 * (q + 1) = 3 ^ 3 * (q + 1) := by norm_num
      _ ≤ Nat.card Ahat := hcard
      _ ≤ 3 * Nat.card Cg := hA_le
      _ ≤ 3 * (3 * (q + 1)) := Nat.mul_le_mul_left 3 hCg_le
      _ = 9 * (q + 1) := by ring
  have h2 : 9 * (q + 1) < 27 * (q + 1) := by
    have hpos : 0 < q + 1 := Nat.succ_pos q
    nlinarith
  exact absurd h1 (not_le.mpr h2)

end CFSG.StandardType.TablePThreeKG

end
