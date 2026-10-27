module

public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanSL2
public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanEig
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Combinatorics.Colex
public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Higman

open Matrix
open scoped MatrixGroups

section Tens

variable {K : Type} [Field K] [CharP K 2] {k : Type} [Field k] [Algebra K k]

@[expose] def frobK (k : Type) [Field k] [Algebra K k] (i : ℕ) : K →+* k :=
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  (algebraMap K k).comp (iterateFrobenius K 2 i)

theorem frobK_apply (i : ℕ) (a : K) : frobK k i a = algebraMap K k (a ^ 2 ^ i) := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  simp [frobK, iterateFrobenius_def]

@[expose] def Amat (i : ℕ) (g : SL(2, K)) : Matrix (Fin 2) (Fin 2) k :=
  (g : Matrix (Fin 2) (Fin 2) K).map (frobK k i)

theorem Amat_mul (i : ℕ) (g h : SL(2, K)) : (Amat i (g * h) : Matrix (Fin 2) (Fin 2) k) =
    Amat i g * Amat i h := by
  simp only [Amat, Matrix.SpecialLinearGroup.coe_mul]
  exact Matrix.map_mul

theorem Amat_one (i : ℕ) : (Amat i (1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) k) = 1 := by
  simp [Amat]

@[expose] def kron (S : Finset ℕ) (M : ↥S → Matrix (Fin 2) (Fin 2) k) :
    Matrix (↥S → Fin 2) (↥S → Fin 2) k :=
  fun ε' ε => ∏ i : ↥S, M i (ε' i) (ε i)

theorem kron_mul (S : Finset ℕ) (M N : ↥S → Matrix (Fin 2) (Fin 2) k) :
    kron S (fun i => M i * N i) = kron S M * kron S N := by
  ext ε' ε
  simp only [kron, Matrix.mul_apply]
  have h := Finset.prod_univ_sum (fun i : ↥S => (Finset.univ : Finset (Fin 2)))
    (fun i j => M i (ε' i) j * N i j (ε i))
  simp only [Fintype.piFinset_univ] at h
  rw [h]
  exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib

theorem kron_one (S : Finset ℕ) : kron S (fun _ => (1 : Matrix (Fin 2) (Fin 2) k)) = 1 := by
  ext ε' ε
  simp only [kron, Matrix.one_apply]
  by_cases h : ε' = ε
  · subst h
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

@[expose] def TRep (S : Finset ℕ) : Representation k SL(2, K) ((↥S → Fin 2) → k) where
  toFun g := Matrix.mulVecLin (kron S fun i => (Amat (i : ℕ) g : Matrix (Fin 2) (Fin 2) k))
  map_one' := by
    simp only [Amat_one, kron_one]
    exact Matrix.mulVecLin_one
  map_mul' g h := by
    simp only [Amat_mul, kron_mul]
    exact Matrix.mulVecLin_mul _ _

theorem TRep_apply (S : Finset ℕ) (g : SL(2, K)) (Φ : (↥S → Fin 2) → k) (ε' : ↥S → Fin 2) :
    TRep S g Φ ε' = ∑ ε : ↥S → Fin 2, (∏ i : ↥S, (Amat (i : ℕ) g : Matrix (Fin 2) (Fin 2) k)
      (ε' i) (ε i)) * Φ ε := by
  rfl

theorem Amat_uMat (i : ℕ) (a : K) :
    (Amat i (uMat a) : Matrix (Fin 2) (Fin 2) k) = !![1, algebraMap K k a ^ 2 ^ i; 0, 1] := by
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Amat, frobK_apply]

theorem Amat_hMat (i : ℕ) (c : Kˣ) :
    (Amat i (hMat c) : Matrix (Fin 2) (Fin 2) k) =
      !![algebraMap K k (c : K) ^ 2 ^ i, 0; 0, algebraMap K k ((c⁻¹ : Kˣ) : K) ^ 2 ^ i] := by
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Amat, frobK_apply]

theorem Amat_wMat (i : ℕ) :
    (Amat i (wMat : SL(2, K)) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; 1, 0] := by
  ext x y
  fin_cases x <;> fin_cases y <;> simp [Amat, frobK_apply]

theorem TRep_single (S : Finset ℕ) (g : SL(2, K)) (ε₀ ε' : ↥S → Fin 2) :
    TRep S g (Pi.single ε₀ (1 : k)) ε' =
      ∏ i : ↥S, (Amat (i : ℕ) g : Matrix (Fin 2) (Fin 2) k) (ε' i) (ε₀ i) := by
  rw [TRep_apply, Finset.sum_eq_single ε₀]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

@[expose] def wt (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2 ^ i

@[expose] def eR (S : Finset ℕ) (ε : ↥S → Fin 2) : ℕ :=
  ∑ i : ↥S, if ε i = 0 then 0 else 2 ^ (i : ℕ)

@[expose] def eC (S : Finset ℕ) (ε : ↥S → Fin 2) : ℕ :=
  ∑ i : ↥S, if ε i = 0 then 2 ^ (i : ℕ) else 0

theorem fin2_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

theorem TRep_u_delta0 (S : Finset ℕ) (a : K) :
    TRep S (uMat a) (Pi.single (0 : ↥S → Fin 2) (1 : k)) = Pi.single (0 : ↥S → Fin 2) (1 : k) := by
  funext ε'
  rw [TRep_single]
  have : ∀ i : ↥S, (Amat (i : ℕ) (uMat a) : Matrix (Fin 2) (Fin 2) k) (ε' i) ((0 : ↥S → Fin 2) i) =
      if ε' i = 0 then 1 else 0 := by
    intro i
    rw [Amat_uMat]
    rcases fin2_cases (ε' i) with h | h <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_boole, Pi.single_apply]
  simp [funext_iff]

theorem TRep_h_delta0 (S : Finset ℕ) (c : Kˣ) :
    TRep S (hMat c) (Pi.single (0 : ↥S → Fin 2) (1 : k)) =
      (algebraMap K k (c : K) ^ wt S) • Pi.single (0 : ↥S → Fin 2) (1 : k) := by
  funext ε'
  rw [TRep_single]
  have : ∀ i : ↥S, (Amat (i : ℕ) (hMat c) : Matrix (Fin 2) (Fin 2) k) (ε' i)
      ((0 : ↥S → Fin 2) i) = if ε' i = 0 then algebraMap K k (c : K) ^ 2 ^ (i : ℕ) else 0 := by
    intro i
    rw [Amat_hMat]
    rcases fin2_cases (ε' i) with h | h <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_ite_zero, Pi.smul_apply,
    Pi.single_apply]
  by_cases h : ε' = 0
  · subst h
    simp only [Pi.zero_apply, implies_true, if_true, smul_eq_mul, mul_one]
    rw [Finset.prod_pow_eq_pow_sum, wt, ← Finset.sum_coe_sort S]
  · have h' : ¬ ∀ i ∈ (Finset.univ : Finset ↥S), ε' i = 0 := fun hh =>
      h (funext fun i => hh i (Finset.mem_univ i))
    rw [if_neg h', if_neg h, smul_zero]

theorem TRep_w_delta0 (S : Finset ℕ) :
    TRep S (wMat : SL(2, K)) (Pi.single (0 : ↥S → Fin 2) (1 : k)) =
      Pi.single (fun _ => (1 : Fin 2) : ↥S → Fin 2) (1 : k) := by
  funext ε'
  rw [TRep_single]
  have : ∀ i : ↥S, (Amat (i : ℕ) (wMat : SL(2, K)) : Matrix (Fin 2) (Fin 2) k) (ε' i)
      ((0 : ↥S → Fin 2) i) = if ε' i = 1 then 1 else 0 := by
    intro i
    rw [Amat_wMat]
    rcases fin2_cases (ε' i) with h | h <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_boole, Pi.single_apply]
  simp [funext_iff]

theorem TRep_u_delta1 (S : Finset ℕ) (a : K) (ε' : ↥S → Fin 2) :
    TRep S (uMat a) (Pi.single (fun _ => (1 : Fin 2) : ↥S → Fin 2) (1 : k)) ε' =
      algebraMap K k a ^ eC S ε' := by
  rw [TRep_single]
  have : ∀ i : ↥S, (Amat (i : ℕ) (uMat a) : Matrix (Fin 2) (Fin 2) k) (ε' i) 1 =
      algebraMap K k a ^ (if ε' i = 0 then 2 ^ (i : ℕ) else 0) := by
    intro i
    rw [Amat_uMat]
    rcases fin2_cases (ε' i) with h | h <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_pow_eq_pow_sum, eC]

theorem TRep_u_row0 (S : Finset ℕ) (a : K) (Φ : (↥S → Fin 2) → k) :
    TRep S (uMat a) Φ 0 = ∑ ε : ↥S → Fin 2, algebraMap K k a ^ eR S ε * Φ ε := by
  rw [TRep_apply]
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1
  have : ∀ i : ↥S, (Amat (i : ℕ) (uMat a) : Matrix (Fin 2) (Fin 2) k) ((0 : ↥S → Fin 2) i) (ε i) =
      algebraMap K k a ^ (if ε i = 0 then 0 else 2 ^ (i : ℕ)) := by
    intro i
    rw [Amat_uMat]
    rcases fin2_cases (ε i) with h | h <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_pow_eq_pow_sum, eR]

theorem monomial_indep [Finite K] {ι : Type*} [Fintype ι] (ex : ι → ℕ)
    (hinj : Function.Injective ex) (hlt : ∀ i, ex i < Nat.card K) (c : ι → k)
    (h : ∀ a : K, ∑ i, c i * algebraMap K k a ^ ex i = 0) : ∀ i, c i = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set P : Polynomial k := ∑ i, Polynomial.C (c i) * Polynomial.X ^ ex i with hPdef
  have hroot : ∀ x ∈ (Finset.univ : Finset K).image (algebraMap K k), P.eval x = 0 := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
    simp only [hPdef, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact h a
  have hcard : ((Finset.univ : Finset K).image (algebraMap K k)).card = Nat.card K := by
    rw [Finset.card_image_of_injective _ (algebraMap K k).injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hdeg : P.natDegree < ((Finset.univ : Finset K).image (algebraMap K k)).card := by
    rw [hcard]
    have : P.natDegree ≤ Nat.card K - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
      have := hlt i
      omega
    have hq : 0 < Nat.card K := Nat.card_pos
    omega
  have hP : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P _ hroot hdeg
  intro i
  have h1 := congrArg (fun p : Polynomial k => p.coeff (ex i)) hP
  simp only [hPdef, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at h1
  rw [Finset.sum_eq_single i] at h1
  · simpa using h1
  · intro j _ hj
    have : ex i ≠ ex j := fun hh => hj (hinj hh).symm
    simp [this]
  · simp

@[expose] def eP (S : Finset ℕ) (p : ↥S → Prop) [DecidablePred p] : ℕ :=
  ∑ i : ↥S, if p i then 2 ^ (i : ℕ) else 0

theorem eP_eq_sum (S : Finset ℕ) (p : ↥S → Prop) [DecidablePred p] :
    eP S p = ∑ j ∈ (Finset.univ.filter p).map (Function.Embedding.subtype _), 2 ^ j := by
  rw [Finset.sum_map, Finset.sum_filter]
  rfl

theorem eP_iff_of_eq (S : Finset ℕ) (p q : ↥S → Prop) [DecidablePred p] [DecidablePred q]
    (h : eP S p = eP S q) : ∀ i, p i ↔ q i := by
  rw [eP_eq_sum, eP_eq_sum] at h
  have h2 := Finset.geomSum_injective (le_refl 2) h
  intro i
  have := congrArg (fun A : Finset ℕ => (i : ℕ) ∈ A) h2
  simpa using this

theorem eP_lt (S : Finset ℕ) {n : ℕ} (hS : ∀ i ∈ S, i < n) (p : ↥S → Prop) [DecidablePred p] :
    eP S p < 2 ^ n := by
  rw [eP_eq_sum]
  refine Nat.geomSum_lt (le_refl 2) ?_
  intro j hj
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
  exact hS i i.2

theorem eP_true (S : Finset ℕ) : eP S (fun _ => True) = wt S := by
  simp only [eP, if_true, wt]
  exact Finset.sum_coe_sort S (fun i => 2 ^ i)

theorem eP_le_wt (S : Finset ℕ) (p : ↥S → Prop) [DecidablePred p] : eP S p ≤ wt S := by
  unfold eP wt
  rw [← Finset.sum_coe_sort S]
  exact Finset.sum_le_sum fun i _ => by split_ifs <;> simp

theorem eP_eq_wt_iff (S : Finset ℕ) (p : ↥S → Prop) [DecidablePred p] :
    eP S p = wt S ↔ ∀ i, p i := by
  constructor
  · intro h
    rw [← eP_true] at h
    intro i
    exact (eP_iff_of_eq S p (fun _ => True) h i).2 trivial
  · intro h
    rw [← eP_true]
    simp [eP, h]

theorem wt_le (S : Finset ℕ) {n : ℕ} (hS : ∀ i ∈ S, i < n) : wt S < 2 ^ n := by
  exact Nat.geomSum_lt (le_refl 2) hS

theorem wt_eq_iff (S : Finset ℕ) {n : ℕ} (hS : ∀ i ∈ S, i < n) :
    wt S = 2 ^ n - 1 ↔ S = Finset.range n := by
  have h1 : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
    have := Nat.geomSum_eq (le_refl 2) n
    simpa using this
  constructor
  · intro h
    refine Finset.geomSum_injective (le_refl 2) ?_
    show ∑ i ∈ S, 2 ^ i = ∑ i ∈ Finset.range n, 2 ^ i
    rw [h1]
    exact h
  · rintro rfl
    simpa [wt] using h1

theorem eR_eq_eP (S : Finset ℕ) (ε : ↥S → Fin 2) : eR S ε = eP S (fun i => ε i ≠ 0) := by
  unfold eR eP
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i = 0 <;> simp [h]

theorem eC_eq_eP (S : Finset ℕ) (ε : ↥S → Fin 2) : eC S ε = eP S (fun i => ε i = 0) := rfl

theorem fin2_ext_of_ne_iff {x y : Fin 2} (h : x ≠ 0 ↔ y ≠ 0) : x = y := by
  rcases fin2_cases x with hx | hx <;> rcases fin2_cases y with hy | hy <;> simp_all

theorem eR_injective (S : Finset ℕ) : Function.Injective (eR S) := by
  intro ε ε' h
  rw [eR_eq_eP, eR_eq_eP] at h
  funext i
  exact fin2_ext_of_ne_iff (eP_iff_of_eq S _ _ h i)

theorem eC_injective (S : Finset ℕ) : Function.Injective (eC S) := by
  intro ε ε' h
  rw [eC_eq_eP, eC_eq_eP] at h
  funext i
  have := eP_iff_of_eq S _ _ h i
  rcases fin2_cases (ε i) with hx | hx <;> rcases fin2_cases (ε' i) with hy | hy <;>
    simp_all

theorem eR_zero (S : Finset ℕ) : eR S 0 = 0 := by
  simp [eR]

theorem eR_lt (S : Finset ℕ) {n : ℕ} (hS : ∀ i ∈ S, i < n) (ε : ↥S → Fin 2) :
    eR S ε < 2 ^ n := by
  rw [eR_eq_eP]
  exact eP_lt S hS _

theorem eC_lt (S : Finset ℕ) {n : ℕ} (hS : ∀ i ∈ S, i < n) (ε : ↥S → Fin 2) :
    eC S ε < 2 ^ n := by
  rw [eC_eq_eP]
  exact eP_lt S hS _

theorem fixed_eq_smul [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < n) (Φ : (↥S → Fin 2) → k) (hfix : ∀ a : K, TRep S (uMat a) Φ = Φ) :
    Φ = Φ 0 • Pi.single (0 : ↥S → Fin 2) (1 : k) := by
  classical
  set c : (↥S → Fin 2) → k := fun ε => if ε = 0 then 0 else Φ ε with hc
  have hzero : ∀ a : K, ∑ ε, c ε * algebraMap K k a ^ eR S ε = 0 := by
    intro a
    have h1 := TRep_u_row0 S a Φ
    rw [hfix a] at h1
    have h2 : ∀ ε : ↥S → Fin 2, algebraMap K k a ^ eR S ε * Φ ε =
        c ε * algebraMap K k a ^ eR S ε + (if ε = 0 then Φ 0 else 0) := by
      intro ε
      by_cases h : ε = 0
      · subst h; simp [hc, eR_zero]
      · simp [hc, h, mul_comm]
    rw [Finset.sum_congr rfl fun ε _ => h2 ε, Finset.sum_add_distrib] at h1
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    linear_combination -h1
  have hc0 := monomial_indep (K := K) (k := k) (eR S) (eR_injective S)
    (fun ε => by rw [hn]; exact eR_lt S hS ε) c hzero
  funext ε
  by_cases h : ε = 0
  · subst h; simp
  · have := hc0 ε
    simp only [hc, if_neg h] at this
    simp [Pi.single_apply, h, this]

theorem orbitSpan_eq_top [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < n) :
    CFSG.Quasithin.SmithCurtis.orbitSpan (TRep (K := K) (k := k) S)
      (Pi.single (0 : ↥S → Fin 2) (1 : k)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  refine hf0 ?_
  have hvan : ∀ a : K, ∑ ε' : ↥S → Fin 2,
      f (fun j => if ε' = j then (1 : k) else 0) * algebraMap K k a ^ eC S ε' = 0 := by
    intro a
    have hmem : TRep (K := K) (k := k) S (uMat a * wMat) (Pi.single (0 : ↥S → Fin 2) (1 : k)) ∈
        CFSG.Quasithin.SmithCurtis.orbitSpan (TRep (K := K) (k := k) S)
          (Pi.single (0 : ↥S → Fin 2) (1 : k)) :=
      Submodule.subset_span ⟨uMat a * wMat, rfl⟩
    have h0 := hker hmem
    rw [LinearMap.mem_ker, map_mul, Module.End.mul_apply, TRep_w_delta0,
      LinearMap.pi_apply_eq_sum_univ f] at h0
    calc _ = ∑ i, TRep (K := K) (k := k) S (uMat a)
          (Pi.single (fun _ => (1 : Fin 2) : ↥S → Fin 2) (1 : k)) i •
          f (fun j => if i = j then (1 : k) else 0) := by
          refine Finset.sum_congr rfl fun ε' _ => ?_
          rw [TRep_u_delta1, smul_eq_mul, mul_comm]
      _ = 0 := h0
  have hc := monomial_indep (K := K) (k := k) (eC S) (eC_injective S)
    (fun ε => by rw [hn]; exact eC_lt S hS ε) _ hvan
  refine LinearMap.ext fun Φ => ?_
  rw [LinearMap.pi_apply_eq_sum_univ f Φ]
  simp [hc]

theorem eC_eq_pred_iff {n : ℕ} (S : Finset ℕ) (hS : ∀ i ∈ S, i < n) (ε : ↥S → Fin 2) :
    eC S ε = 2 ^ n - 1 ↔ S = Finset.range n ∧ ε = 0 := by
  constructor
  · intro h
    have h1 := eP_le_wt S (fun i => ε i = 0)
    have h2 := wt_le S hS
    have h3 : wt S = 2 ^ n - 1 := by
      rw [eC_eq_eP] at h
      omega
    refine ⟨(wt_eq_iff S hS).1 h3, ?_⟩
    have h4 : eP S (fun i => ε i = 0) = wt S := by rw [← eC_eq_eP, h, h3]
    funext i
    exact (eP_eq_wt_iff S _).1 h4 i
  · rintro ⟨rfl, rfl⟩
    rw [eC_eq_eP]
    have : eP (Finset.range n) (fun i => (0 : ↥(Finset.range n) → Fin 2) i = 0) =
        wt (Finset.range n) := (eP_eq_wt_iff _ _).2 fun i => rfl
    rw [this]
    exact (wt_eq_iff _ (fun i hi => Finset.mem_range.1 hi)).2 rfl

theorem sum_pow_eq_units (K : Type) [Field K] [Fintype K] [DecidableEq K] {i : ℕ} (hi : i ≠ 0) :
    ∑ x : K, x ^ i = ∑ x : Kˣ, (x : K) ^ i := by
  let φ : Kˣ ↪ K := ⟨fun x ↦ x, Units.val_injective⟩
  have : Finset.univ.map φ = Finset.univ \ {0} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    ∑ x : K, x ^ i = ∑ x ∈ Finset.univ \ {(0 : K)}, x ^ i := by
      rw [← Finset.sum_sdiff ({0} : Finset K).subset_univ, Finset.sum_singleton, zero_pow hi,
        add_zero]
    _ = ∑ x : Kˣ, (x : K) ^ i := by simp [φ, ← this, Finset.univ.sum_map φ]

theorem sum_pow_card_sub_one (K : Type) [Field K] [Fintype K] [DecidableEq K] :
    ∑ x : K, x ^ (Fintype.card K - 1) = -1 := by
  have hpos : 1 < Fintype.card K := Fintype.one_lt_card
  rw [sum_pow_eq_units K (by omega), FiniteField.sum_pow_units K (Fintype.card K - 1),
    if_pos dvd_rfl]

@[expose] noncomputable def uEquiv (K : Type) [Field K] [CharP K 2] : K ≃ ↥(Usub K) :=
  Equiv.ofBijective (fun a => ⟨uMat a, a, rfl⟩) ⟨fun a b h => by
    have h1 := congrArg (fun g : ↥(Usub K) => (g : SL(2, K))) h
    have h2 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
    simpa using h2, fun ⟨_, a, rfl⟩ => ⟨a, rfl⟩⟩

theorem heckeT_sl2 [Fintype K] {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k SL(2, K) V) (v : V) :
    (sl2Datum (K := K)).heckeT ρ 0 v = ∑ a : K, ρ (uMat a * wMat) v := by
  classical
  letI : Fintype ↥((sl2Datum (K := K)).X 0) := (inferInstance : Fintype ↥(Usub K))
  rw [CFSG.Quasithin.SmithCurtis.CurtisDatum.heckeT_apply]
  exact (Fintype.sum_equiv (uEquiv K : K ≃ ↥((sl2Datum (K := K)).X 0))
    (fun a => ρ (uMat a * wMat) v)
    (fun x => ρ ((x : SL(2, K)) * (sl2Datum (K := K)).n 0) v) (fun a => rfl)).symm

theorem heckeT_delta0 [Finite K] [CharP k 2] {n : ℕ} (hn : Nat.card K = 2 ^ n) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < n) :
    (sl2Datum (K := K)).heckeT (TRep (K := K) (k := k) S) 0 (Pi.single (0 : ↥S → Fin 2) (1 : k)) =
      (if S = Finset.range n then (1 : k) else 0) • Pi.single (0 : ↥S → Fin 2) (1 : k) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [heckeT_sl2]
  have hq : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hn]
  have h1 : ∀ a : K, TRep (K := K) (k := k) S (uMat a * wMat) (Pi.single (0 : ↥S → Fin 2) (1 : k)) =
      TRep (K := K) (k := k) S (uMat a)
        (Pi.single (fun _ => (1 : Fin 2) : ↥S → Fin 2) (1 : k)) := by
    intro a
    rw [map_mul, Module.End.mul_apply, TRep_w_delta0]
  simp only [h1]
  funext ε'
  rw [Finset.sum_apply]
  have h2 : ∀ a : K, TRep (K := K) (k := k) S (uMat a)
      (Pi.single (fun _ => (1 : Fin 2) : ↥S → Fin 2) (1 : k)) ε' =
      algebraMap K k (a ^ eC S ε') := fun a => by
    rw [map_pow]
    exact TRep_u_delta1 S a ε'
  rw [Finset.sum_congr rfl fun a _ => h2 a, ← map_sum, Pi.smul_apply, Pi.single_apply]
  by_cases hc : S = Finset.range n ∧ ε' = 0
  · obtain ⟨rfl, rfl⟩ := hc
    have hj : eC (Finset.range n) 0 = Fintype.card K - 1 := by
      rw [hq]; exact (eC_eq_pred_iff _ (fun i hi => Finset.mem_range.1 hi) 0).2 ⟨rfl, rfl⟩
    rw [hj, sum_pow_card_sub_one K]
    simp [CharTwo.neg_eq]
  · have hj : eC S ε' < Fintype.card K - 1 := by
      have h3 := eC_lt S hS ε'
      have h4 : eC S ε' ≠ 2 ^ n - 1 := fun h => hc ((eC_eq_pred_iff S hS ε').1 h)
      rw [hq]
      omega
    rw [FiniteField.sum_pow_lt_card_sub_one K _ hj, map_zero]
    by_cases hS' : S = Finset.range n
    · have : ε' ≠ 0 := fun h => hc ⟨hS', h⟩
      simp [hS', this]
    · simp [hS']

theorem kron_mulVec_prod (S : Finset ℕ) (M : ↥S → Matrix (Fin 2) (Fin 2) k)
    (v : ↥S → Fin 2 → k) :
    kron S M *ᵥ (fun ε => ∏ i : ↥S, v i (ε i)) = fun ε' => ∏ i : ↥S, (M i *ᵥ v i) (ε' i) := by
  funext ε'
  simp only [Matrix.mulVec, dotProduct, kron]
  have h := Finset.prod_univ_sum (fun i : ↥S => (Finset.univ : Finset (Fin 2)))
    (fun i j => M i (ε' i) j * v i j)
  simp only [Fintype.piFinset_univ] at h
  rw [Finset.prod_congr rfl fun i _ => (rfl : (∑ j, M i (ε' i) j * v i j) = _), h]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Finset.prod_mul_distrib]

theorem TRep_prod_eigen (S : Finset ℕ) (g : SL(2, K)) (v : ↥S → Fin 2 → k) (l : ↥S → k)
    (hv : ∀ i : ↥S, (Amat (i : ℕ) g : Matrix (Fin 2) (Fin 2) k) *ᵥ v i = l i • v i) :
    TRep S g (fun ε => ∏ i : ↥S, v i (ε i)) =
      (∏ i : ↥S, l i) • (fun ε => ∏ i : ↥S, v i (ε i)) := by
  show Matrix.mulVec _ _ = _
  rw [kron_mulVec_prod]
  funext ε'
  simp only [hv, Pi.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]

theorem Amat_sq (i : ℕ) (d : SL(2, K)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    (Amat i d : Matrix (Fin 2) (Fin 2) k) * Amat i d = Amat i d + 1 := by
  unfold Amat
  rw [← Matrix.map_mul, sl2_sq_eq d hd3 hd1, Matrix.map_add _ (fun a b => map_add _ a b),
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem Amat_ne_scalar (i : ℕ) (d : SL(2, K)) (hd1 : d ≠ 1) (c : k) :
    (Amat i d : Matrix (Fin 2) (Fin 2) k) ≠ c • (1 : Matrix (Fin 2) (Fin 2) k) := by
  intro h
  apply sl2_ne_scalar d hd1 ((d : Matrix (Fin 2) (Fin 2) K) 0 0)
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Amat, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul] at h01 h10 h00 h11
  have hinj : Function.Injective (frobK (K := K) k i) := (frobK (K := K) k i).injective
  have hb : (d : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := hinj (by simpa using h01)
  have hc : (d : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hinj (by simpa using h10)
  have he : (d : Matrix (Fin 2) (Fin 2) K) 1 1 = (d : Matrix (Fin 2) (Fin 2) K) 0 0 :=
    hinj (by simp at h00 h11; rw [h00, h11])
  ext x y
  fin_cases x <;> fin_cases y <;> simp [hb, hc, he]

theorem exists_fixed_vec [CharP k 2] {ω : k} (hω : ω ^ 2 + ω + 1 = 0) (d : SL(2, K))
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (S : Finset ℕ) (hS : 2 ≤ S.card) :
    ∃ Φ : (↥S → Fin 2) → k, Φ ≠ 0 ∧ TRep S d Φ = Φ := by
  classical
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hω' : (ω + 1) ^ 2 + (ω + 1) + 1 = 0 := by linear_combination hω + (ω + 1) * h2
  have hω2 : ω + 1 = ω ^ 2 := by linear_combination -hω + (ω + 1) * h2
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  choose vp hvp0 hvp using fun i : ↥S =>
    exists_eigenvector (Amat (i : ℕ) d) (Amat_sq (i : ℕ) d hd3 hd1) hω
      (Amat_ne_scalar (i : ℕ) d hd1)
  choose vm hvm0 hvm using fun i : ↥S =>
    exists_eigenvector (Amat (i : ℕ) d) (Amat_sq (i : ℕ) d hd3 hd1) hω'
      (Amat_ne_scalar (i : ℕ) d hd1)
  set r := (2 * S.card) % 3 with hr
  have hrle : r ≤ (Finset.univ : Finset ↥S).card := by
    rw [Finset.card_univ, Fintype.card_coe]
    omega
  obtain ⟨P, -, hP⟩ := Finset.exists_subset_card_eq hrle
  let v : ↥S → Fin 2 → k := fun i => if i ∈ P then vp i else vm i
  let l : ↥S → k := fun i => if i ∈ P then ω else ω + 1
  have hv : ∀ i : ↥S, (Amat (i : ℕ) d : Matrix (Fin 2) (Fin 2) k) *ᵥ v i = l i • v i := by
    intro i
    by_cases hi : i ∈ P
    · simp only [v, l, if_pos hi]; exact hvp i
    · simp only [v, l, if_neg hi]; exact hvm i
  have hl : ∏ i : ↥S, l i = 1 := by
    rw [← Finset.prod_mul_prod_compl P l]
    rw [Finset.prod_congr rfl fun i hi => (if_pos hi : l i = ω),
      Finset.prod_congr rfl fun i hi => (if_neg (Finset.mem_compl.1 hi) : l i = ω + 1),
      Finset.prod_const, Finset.prod_const, Finset.card_compl, Fintype.card_coe, hP, hω2,
      ← pow_mul, ← pow_add]
    have : r + 2 * (S.card - r) = 3 * (2 * S.card / 3) := by omega
    rw [this, pow_mul, hω3, one_pow]
  refine ⟨fun ε => ∏ i : ↥S, v i (ε i), ?_, ?_⟩
  · have hex : ∀ i : ↥S, ∃ j : Fin 2, v i j ≠ 0 := by
      intro i
      by_cases hi : i ∈ P
      · obtain ⟨j, hj⟩ := Function.ne_iff.1 (show vp i ≠ 0 from hvp0 i)
        exact ⟨j, by simpa [v, hi] using hj⟩
      · obtain ⟨j, hj⟩ := Function.ne_iff.1 (show vm i ≠ 0 from hvm0 i)
        exact ⟨j, by simpa [v, hi] using hj⟩
    choose ε hε using hex
    intro h
    have := congrFun h ε
    simp only [Pi.zero_apply] at this
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hε i) this
  · rw [TRep_prod_eigen S d v l hv, hl, one_smul]

theorem TRep_empty (g : SL(2, K)) (Φ : (↥(∅ : Finset ℕ) → Fin 2) → k) :
    TRep (∅ : Finset ℕ) g Φ = Φ := by
  funext ε'
  rw [TRep_apply]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  exact Fintype.sum_subsingleton _ ε'

@[expose] def natEquiv (k : Type) [Field k] (i : ℕ) :
    ((↥({i} : Finset ℕ) → Fin 2) → k) ≃ₗ[k] (Fin 2 → k) where
  toFun Φ j := Φ (fun _ => j)
  invFun w ε := w (ε ⟨i, Finset.mem_singleton_self i⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv Φ := by
    funext ε
    show Φ (fun _ => ε ⟨i, Finset.mem_singleton_self i⟩) = Φ ε
    congr 1
    funext x
    have : x = ⟨i, Finset.mem_singleton_self i⟩ := Subsingleton.elim _ _
    rw [this]
  right_inv w := rfl

theorem natEquiv_TRep (i : ℕ) (g : SL(2, K)) (Φ : (↥({i} : Finset ℕ) → Fin 2) → k) :
    natEquiv k i (TRep ({i} : Finset ℕ) g Φ) =
      (Amat i g : Matrix (Fin 2) (Fin 2) k) *ᵥ natEquiv k i Φ := by
  funext j
  show TRep ({i} : Finset ℕ) g Φ (fun _ => j) = _
  rw [TRep_apply]
  simp only [Matrix.mulVec, dotProduct]
  refine Fintype.sum_equiv (Equiv.funUnique ↥({i} : Finset ℕ) (Fin 2)) _ _ fun ε => ?_
  have hε : ε = fun _ => ε default := by
    funext x
    rw [Subsingleton.elim x default]
  rw [Fintype.prod_unique]
  show _ * Φ ε = _ * Φ (fun _ => ε default)
  rw [← hε]
  rfl

theorem delta0_ne_zero (S : Finset ℕ) :
    (Pi.single (0 : ↥S → Fin 2) (1 : k) : (↥S → Fin 2) → k) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

theorem TRep_isSimple [Finite K] [CharP k 2] {n : ℕ} (hn : Nat.card K = 2 ^ n) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < n) :
    CFSG.Quasithin.SmithCurtis.IsSimpleRep (TRep (K := K) (k := k) S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (sl2Datum (K := K)).isSimpleRep_of_fixU (TRep (K := K) (k := k) S)
    (y := Pi.single (0 : ↥S → Fin 2) (1 : k)) ?_ (orbitSpan_eq_top hn S hS)
  intro x hx
  exact ⟨x 0, fixed_eq_smul hn S hS x fun a => hx (uMat a) ⟨a, rfl⟩⟩

theorem TRep_isCurtisType [Finite K] [CharP k 2] {n : ℕ} (hn : Nat.card K = 2 ^ n)
    (S : Finset ℕ) (hS : ∀ i ∈ S, i < n) (χ : SL(2, K) → k)
    (hχ : ∀ r : Kˣ, χ (hMat r) = algebraMap K k (r : K) ^ wt S) :
    (sl2Datum (K := K)).IsCurtisType (TRep (K := K) (k := k) S)
      (Pi.single (0 : ↥S → Fin 2) (1 : k)) χ
      (fun _ => if S = Finset.range n then (1 : k) else 0) := by
  refine ⟨?_, delta0_ne_zero S, ?_, ?_⟩
  · intro u hu
    obtain ⟨a, rfl⟩ := hu
    exact TRep_u_delta0 S a
  · rintro h ⟨r, rfl⟩
    rw [hχ r]
    exact TRep_h_delta0 S r
  · intro s
    have hs : s = 0 := Subsingleton.elim s 0
    subst hs
    exact heckeT_delta0 hn S hS

end Tens
end CFSG.LocalAnalysis.UniquenessCase.UCK.Higman
