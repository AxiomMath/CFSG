module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped commutatorElement

private lemma aeval_diagonal_eq {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (w : ι → K) (g : Polynomial K) :
    Polynomial.aeval (Matrix.diagonal w) g = Matrix.diagonal (fun a => g.eval (w a)) := by
  change Polynomial.aeval ((Matrix.diagonalAlgHom K) w) g = _
  rw [Polynomial.aeval_algHom_apply, Matrix.diagonalAlgHom_apply]
  ext a b; by_cases h : a = b <;> simp [h, Polynomial.aeval_fn_apply]

private lemma eq_diagonal_of_mem_adjoin {K : Type} [Field K] {m : ℕ} (t : Fin m → Kˣ)
    {y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hy : y ∈ Algebra.adjoin K (Units.val ''
      ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} : Set (GL (Fin m ⊕ Fin m) K)))) :
    ∃ g : Polynomial K, y = Matrix.diagonal (fun a => g.eval (diagSpEntry t a)) := by
  rw [Set.image_singleton] at hy; rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨g, hg⟩ := hy; refine ⟨g, hg.symm.trans ?_⟩
  rw [show ((((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K)) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal (diagSpEntry t) from by
    rw [← mat_apply, mat_diagSp]]
  exact aeval_diagonal_eq (diagSpEntry t) g

private lemma formAdj_diagonal_eq {K : Type} [Field K] [CharP K 2] {m : ℕ}
    (u : Fin m ⊕ Fin m → K) : formAdj (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (Matrix.diagonal u) = Matrix.diagonal (u ∘ Equiv.sumComm (Fin m) (Fin m)) := by
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  let G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := Matrix.fromBlocks 0 1 (-1) 0
  have hnegm : (-1 : Matrix (Fin m) (Fin m) K) = 1 := by
    ext i j; rw [Matrix.neg_apply, Matrix.one_apply]; by_cases h : i = j <;> simp [h, hneg]
  have hGG : G * G = 1 := by
    rw [show G = Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) K) 1 (-1) 0 from rfl,
      Matrix.fromBlocks_multiply]
    simp [hnegm, Matrix.fromBlocks_one]
  have hGinv : G⁻¹ = G := Matrix.inv_eq_right_inv hGG
  change G⁻¹ * Matrix.transpose (Matrix.diagonal u) * G = _; rw [Matrix.diagonal_transpose, hGinv]
  set u1 : Fin m → K := fun i => u (Sum.inl i)
  set u2 : Fin m → K := fun i => u (Sum.inr i)
  have hD : Matrix.diagonal u =
      Matrix.fromBlocks (Matrix.diagonal u1) 0 0 (Matrix.diagonal u2) := by
    rw [Matrix.fromBlocks_diagonal]
    congr 1
    funext a
    rcases a with i | i <;> rfl
  rw [hD]; rw [show G = Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) K) 1 (-1) 0 from rfl,
    Matrix.fromBlocks_multiply]
  rw [hnegm]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add, add_zero,
    Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_diagonal]
  congr 1
  funext a
  rcases a with i | i <;> rfl

lemma diagSpEntry_sumComm {K : Type} [Field K] {m : ℕ} (t : Fin m → Kˣ)
    (a : Fin m ⊕ Fin m) :
    diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) = (diagSpEntry t a)⁻¹ := by
  rcases a with i | i <;> simp [Equiv.sumComm]

private lemma card_sub_one_pos {K : Type} [Field K] [Finite K] : 0 < Nat.card K - 1 := by
  have h2 : 1 < Nat.card K := by
    have : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  omega

private lemma fibre_one {K : Type} [Field K] [Finite K] [DecidableEq K] {m : ℕ}
    (t : Fin m → Kˣ) (μ : K) : (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) -
      ((((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - μ • 1) ^ (Nat.card K - 1) =
    Matrix.diagonal (fun a => if diagSpEntry t a = μ then 1 else 0) := by
  classical
  let F : Fintype K := Fintype.ofFinite K
  have hq := card_sub_one_pos (K := K)
  have hqF : 0 < @Fintype.card K F - 1 := by
    rw [← @Nat.card_eq_fintype_card K F]; exact hq
  set b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hbdef
  have hmat : b = Matrix.diagonal (diagSpEntry t) := by rw [hbdef, ← mat_apply, mat_diagSp]
  change (1 : Matrix _ _ K) - (b - μ • 1) ^ (Nat.card K - 1) = _
  have hb1 : b - μ • 1 = Matrix.diagonal (fun a => diagSpEntry t a - μ) := by
    rw [hmat, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  rw [hb1, Matrix.diagonal_pow]; ext a b; by_cases hab : a = b
  · subst hab
    simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply, if_true]
    by_cases h : diagSpEntry t a = μ
    · simp [h, hqF.ne']
    · have hne : diagSpEntry t a - μ ≠ 0 := sub_ne_zero.mpr h
      simp [h, @FiniteField.pow_card_sub_one_eq_one K _ F _ hne]
  · simp [Matrix.sub_apply, hab]

private lemma fibre_pair {K : Type} [Field K] [Finite K] [DecidableEq K] {m : ℕ}
    (t : Fin m → Kˣ) (μ : K) : (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) -
      ((((((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - μ • 1) *
        ((((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - μ⁻¹ • 1)) ^
          (Nat.card K - 1)) =
    Matrix.diagonal (fun a => if diagSpEntry t a = μ ∨ diagSpEntry t a = μ⁻¹ then 1 else 0) := by
  classical
  let F : Fintype K := Fintype.ofFinite K
  have hq := card_sub_one_pos (K := K)
  have hqF : 0 < @Fintype.card K F - 1 := by
    rw [← @Nat.card_eq_fintype_card K F]; exact hq
  set b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hbdef
  have hmat : b = Matrix.diagonal (diagSpEntry t) := by rw [hbdef, ← mat_apply, mat_diagSp]
  change (1 : Matrix _ _ K) - ((b - μ • 1) * (b - μ⁻¹ • 1)) ^ (Nat.card K - 1) = _
  have hb1 : b - μ • 1 = Matrix.diagonal (fun a => diagSpEntry t a - μ) := by
    rw [hmat, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  have hb2 : b - μ⁻¹ • 1 = Matrix.diagonal (fun a => diagSpEntry t a - μ⁻¹) := by
    rw [hmat, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  have hbmul : (b - μ • 1) * (b - μ⁻¹ • 1) =
      Matrix.diagonal (fun a => (diagSpEntry t a - μ) * (diagSpEntry t a - μ⁻¹)) := by
    rw [hb1, hb2, Matrix.diagonal_mul_diagonal]
  rw [hbmul, Matrix.diagonal_pow]; ext a b; by_cases hab : a = b
  · subst hab
    simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply, if_true]
    by_cases h : diagSpEntry t a = μ ∨ diagSpEntry t a = μ⁻¹
    · have hzero : (diagSpEntry t a - μ) * (diagSpEntry t a - μ⁻¹) = 0 := by
        rcases h with h | h
        · rw [h, sub_self, zero_mul]
        · rw [h, sub_self, mul_zero]
      simp [h, hzero, hqF.ne']
    · have h1 : diagSpEntry t a - μ ≠ 0 := fun h0 => h (Or.inl (sub_eq_zero.mp h0))
      have h2 : diagSpEntry t a - μ⁻¹ ≠ 0 := fun h0 => h (Or.inr (sub_eq_zero.mp h0))
      simp [h, @FiniteField.pow_card_sub_one_eq_one K _ F _ (mul_ne_zero h1 h2)]
  · simp [Matrix.sub_apply, hab]

theorem exists_eq_diagonal_of_isPrimAdjIdemIn_diagSp {K : Type} [Field K] [Finite K]
    [CharP K 2] {m : ℕ}
    (t : Fin m → Kˣ) {ε : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (Algebra.adjoin K (Units.val ''
        ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
          Set (GL (Fin m ⊕ Fin m) K)))) ε) : ∃ v : Fin m ⊕ Fin m → K, ε = Matrix.diagonal v ∧
      (∀ a, v a = 0 ∨ v a = 1) ∧ (∀ a c, diagSpEntry t a = diagSpEntry t c → v a = v c) ∧
      (∀ a, v a = v (Equiv.sumComm (Fin m) (Fin m) a)) ∧ (∃ lam : K, lam ≠ 0 ∧ ∀ a, v a = 1 →
        diagSpEntry t a = lam ∨ diagSpEntry t a = lam⁻¹) := by
  classical
  let A : Subalgebra K (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := Algebra.adjoin K (Units.val ''
      ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} : Set (GL (Fin m ⊕ Fin m) K)))
  have hεA : ε ∈ A := hε.1
  obtain ⟨g, hg⟩ := eq_diagonal_of_mem_adjoin t hε.1
  let v : Fin m ⊕ Fin m → K := fun a => g.eval (diagSpEntry t a)
  have hεv : ε = Matrix.diagonal v := hg
  have hidem : IsIdempotentElem ε := hε.2.1
  have hne : ε ≠ 0 := hε.2.2.1
  have hfix : formAdj (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) ε = ε := hε.2.2.2.1
  have hv : ∀ a, v a = 0 ∨ v a = 1 := by
    intro a; have hsq : v a * v a = v a := by
      have h := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K => M a a)
        (show Matrix.diagonal (fun a => v a * v a) = Matrix.diagonal v from by
          rw [← Matrix.diagonal_mul_diagonal, ← hεv, hidem.eq, hεv])
      simpa [Matrix.diagonal_apply] using h
    have h3 : v a * (v a - 1) = 0 := by rw [mul_sub, mul_one, hsq, sub_self]
    rcases mul_eq_zero.mp h3 with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hconst : ∀ a c, diagSpEntry t a = diagSpEntry t c → v a = v c := by
    intro a c h
    change g.eval (diagSpEntry t a) = g.eval (diagSpEntry t c)
    rw [h]
  have hpar : ∀ a, v a = v (Equiv.sumComm (Fin m) (Fin m) a) := by
    intro a; have h := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K => M a a) hfix
    rw [hεv, formAdj_diagonal_eq] at h; simpa [Matrix.diagonal_apply] using h.symm
  have hsuppne : ∃ a, v a = 1 := by
    by_contra h; apply hne; rw [hεv]
    ext a b; have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
    simp [Matrix.diagonal_apply, h0]
  obtain ⟨a₀, ha₀⟩ := hsuppne
  set lam : K := diagSpEntry t a₀ with hlamdef
  have hlamne : lam ≠ 0 := by
    rw [hlamdef]; rcases a₀ with i | i <;> simp
  let p : Fin m ⊕ Fin m → K :=
    fun a => if diagSpEntry t a = lam ∨ diagSpEntry t a = lam⁻¹ then 1 else 0
  have hp : ∀ a, p a = 0 ∨ p a = 1 := by
    intro a; unfold p
    split <;> simp
  have hppar : ∀ a, p (Equiv.sumComm (Fin m) (Fin m) a) = p a := by
    intro a; have hinv : diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) = (diagSpEntry t a)⁻¹ :=
      diagSpEntry_sumComm t a
    change (if diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) = lam ∨
        diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) = lam⁻¹ then 1 else 0) =
      (if diagSpEntry t a = lam ∨ diagSpEntry t a = lam⁻¹ then 1 else 0)
    by_cases h : diagSpEntry t a = lam ∨ diagSpEntry t a = lam⁻¹
    · have h' : diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) = lam ∨
          diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) = lam⁻¹ := by
        rw [hinv]; rcases h with h | h
        · right; rw [h]
        · left; rw [h, inv_inv]
      rw [if_pos h', if_pos h]
    · have h' : ¬(diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) = lam ∨
          diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) = lam⁻¹) := by
        rw [hinv]
        rintro (h' | h')
        · exact h (Or.inr (by have := congrArg (fun x : K => x⁻¹) h'; simpa using this))
        · exact h (Or.inl (by have := congrArg (fun x : K => x⁻¹) h'; simpa using this))
      rw [if_neg h', if_neg h]
  have hπA : Matrix.diagonal p ∈ A := by
    change Matrix.diagonal (fun a => if diagSpEntry t a = lam ∨
      diagSpEntry t a = lam⁻¹ then 1 else 0) ∈ A
    rw [← fibre_pair t lam]
    have hbA : (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) ∈ A :=
      Algebra.mem_adjoin_of_mem (by rw [Set.image_singleton]; exact Set.mem_singleton _)
    exact Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Subalgebra.pow_mem _ (Subalgebra.mul_mem _
        (Subalgebra.sub_mem _ hbA (Subalgebra.smul_mem _ (Subalgebra.one_mem _) lam))
        (Subalgebra.sub_mem _ hbA (Subalgebra.smul_mem _ (Subalgebra.one_mem _) lam⁻¹)))
        (Nat.card K - 1))
  let e : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := ε * Matrix.diagonal p
  have he_eq : e = Matrix.diagonal (fun a => v a * p a) := by
    rw [show e = Matrix.diagonal v * Matrix.diagonal p from by
      rw [show e = ε * Matrix.diagonal p from rfl, hεv], Matrix.diagonal_mul_diagonal]
  have heA : e ∈ A := Subalgebra.mul_mem _ hεA hπA
  have he_idem : IsIdempotentElem e := by
    rw [he_eq, isIdempotentElem_iff, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    rcases hv a with h | h <;> rcases hp a with k | k <;> rw [h, k] <;> ring
  have he_adj : formAdj (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) e = e := by
    rw [he_eq, formAdj_diagonal_eq]
    congr 1
    funext a
    rw [Function.comp_apply, hppar a, hpar a]
  have he_e : e * ε = e := by
    rw [he_eq, hεv, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    rcases hv a with h | h <;> rcases hp a with k | k <;> rw [h, k] <;> ring
  have he_ne : e ≠ 0 := by
    have h1 : e a₀ a₀ = 1 := by
      rw [he_eq, Matrix.diagonal_apply, if_pos rfl]
      have hp1 : p a₀ = 1 := by
        unfold p; rw [if_pos (Or.inl (by rw [hlamdef]))]
      simp [ha₀, hp1]
    intro h0; rw [h0, Matrix.zero_apply] at h1; exact zero_ne_one h1
  rcases hε.2.2.2.2 e heA he_idem he_adj he_e with h0 | he
  · exact absurd h0 he_ne
  have hsupp : ∀ a, v a = 1 → diagSpEntry t a = lam ∨ diagSpEntry t a = lam⁻¹ := by
    intro a ha; by_contra h
    have h1 : p a = 0 := by
      unfold p; rw [if_neg h]
    have hcc := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K => M a a) he
    rw [he_eq, hεv, Matrix.diagonal_apply, if_pos rfl, Matrix.diagonal_apply, if_pos rfl,
      h1, mul_zero, ha] at hcc
    exact zero_ne_one hcc
  exact ⟨v, hεv, hv, hconst, hpar, lam, hlamne, hsupp⟩

theorem diagSp_mul_eq_of_isPrimAdjIdemIn {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (t : Fin m → Kˣ) {ε : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (Algebra.adjoin K (Units.val ''
        ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
          Set (GL (Fin m ⊕ Fin m) K)))) ε)
    (hprim : IsPrimIdemIn (Algebra.adjoin K (Units.val ''
      ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
        Set (GL (Fin m ⊕ Fin m) K)))) ε) :
    ((((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * ε = ε) := by
  classical
  let A : Subalgebra K (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := Algebra.adjoin K (Units.val ''
      ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} : Set (GL (Fin m ⊕ Fin m) K)))
  obtain ⟨v, hεv, hv, hconst, hsym, -, -, -⟩ := exists_eq_diagonal_of_isPrimAdjIdemIn_diagSp t hε
  have hne : ∃ a, v a = 1 := by
    by_contra h; apply hε.2.2.1
    rw [hεv]; ext a b
    have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
    simp [Matrix.diagonal_apply, h0]
  obtain ⟨a0, ha0⟩ := hne
  set lam : K := diagSpEntry t a0 with hlamdef
  have hlamne : lam ≠ 0 := by
    rw [hlamdef]; rcases a0 with i | i <;> simp
  let p : Fin m ⊕ Fin m → K := fun a => if diagSpEntry t a = lam then 1 else 0
  have hp : ∀ a, p a = 0 ∨ p a = 1 := by
    intro a; unfold p; split <;> simp
  have hπA : Matrix.diagonal p ∈ A := by
    change Matrix.diagonal (fun a => if diagSpEntry t a = lam then 1 else 0) ∈ A
    rw [← fibre_one t lam]
    have hbA : (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) ∈ A :=
      Algebra.mem_adjoin_of_mem (by rw [Set.image_singleton]; exact Set.mem_singleton _)
    exact Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Subalgebra.pow_mem _ (Subalgebra.sub_mem _ hbA
        (Subalgebra.smul_mem _ (Subalgebra.one_mem _) lam)) (Nat.card K - 1))
  let e : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := ε * Matrix.diagonal p
  have he_eq : e = Matrix.diagonal (fun a => v a * p a) := by
    rw [show e = Matrix.diagonal v * Matrix.diagonal p from by
      rw [show e = ε * Matrix.diagonal p from rfl, hεv], Matrix.diagonal_mul_diagonal]
  have heA : e ∈ A := Subalgebra.mul_mem _ hε.1 hπA
  have he_idem : IsIdempotentElem e := by
    rw [he_eq, isIdempotentElem_iff, Matrix.diagonal_mul_diagonal]; congr 1; funext a
    rcases hv a with h | h <;> rcases hp a with k | k <;> rw [h, k] <;> ring
  have he_e : e * ε = e := by
    rw [he_eq, hεv, Matrix.diagonal_mul_diagonal]; congr 1; funext a
    rcases hv a with h | h <;> rcases hp a with k | k <;> rw [h, k] <;> ring
  have he_ne : e ≠ 0 := by
    have h1 : e a0 a0 = 1 := by
      rw [he_eq, Matrix.diagonal_apply, if_pos rfl]
      have hp1 : p a0 = 1 := by unfold p; rw [if_pos (by rw [hlamdef])]
      simp [ha0, hp1]
    intro h0; rw [h0, Matrix.zero_apply] at h1; exact zero_ne_one h1
  rcases hprim.2.2.2 e heA he_idem he_e with h0 | he
  · exact absurd h0 he_ne
  have hsupp : ∀ a, v a = 1 → diagSpEntry t a = lam := by
    intro a ha; by_contra h; have h1 : p a = 0 := by unfold p; rw [if_neg h]
    have hcc := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K => M a a) he
    rw [he_eq, hεv, Matrix.diagonal_apply, if_pos rfl, Matrix.diagonal_apply, if_pos rfl,
      h1, mul_zero, ha] at hcc
    exact zero_ne_one hcc
  have hlam_inv : lam = lam⁻¹ := by
    have h1 := hsupp (Equiv.sumComm (Fin m) (Fin m) a0) (by rw [← hsym a0]; exact ha0)
    rw [diagSpEntry_sumComm] at h1; exact h1.symm
  have hlam1 : lam = 1 := by
    have hsq : lam ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [hlam_inv]; exact inv_mul_cancel₀ hlamne
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  rw [hεv, show (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal (diagSpEntry t) from by
    rw [← mat_apply, mat_diagSp], Matrix.diagonal_mul_diagonal]
  congr 1; funext a
  rcases hv a with h | h
  · simp [h]
  · rw [hsupp a h, hlam1, h, mul_one]

end CFSG.StandardType
