module

public import CFSG.RankThree.PartOne.AUTSL.WeightCount
public import CFSG.RankThree.PartOne.AUTSL.DiagWeights
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical

section Core

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {E : Type*} [CommGroup E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def diagOf (f : ι → (E →* Kˣ)) (e : E) : Matrix ι ι K :=
  Matrix.diagonal fun i => ((f i e : Kˣ) : K)

theorem mult_le_twist (f : ι → (E →* Kˣ)) {B : Type*} [CommGroup B] (ιB : B →* E)
    (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B) (hθ3 : ∀ b, θ (θ (θ b)) = b) (j e : ℕ) (he : ¬ 5 ∣ e)
    (A : Matrix ι ι K) (hA : IsUnit A)
    (hrel : ∀ b : B, A * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f (ιB (θ b)) * A) (χ : B →* Kˣ) :
    mult (fun i => (f i).comp ιB) χ ≤
      mult (fun i => (f i).comp ιB) (twist θ (e * 2 ^ j) χ) := by
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let σ : K →+* K := iterateFrobenius K 2 j
  have hσ : ∀ x, σ x = x ^ 2 ^ j := iterateFrobenius_def 2 j
  have : Fintype K := Fintype.ofFinite K
  let d : B → Matrix ι ι K := fun b => Matrix.diagonal fun i => ((f i (ιB b) : Kˣ) : K) ^ e
  let d' : B → Matrix ι ι K := fun b => diagOf f (ιB b)
  have hΘ : ∀ b, A * (d b).map σ = d' (θ b) * A := fun b => by
    have : (d b).map σ =
        Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e) ^ 2 ^ j) := by
      simp only [d]
      rw [Matrix.diagonal_map (map_zero σ)]
      simp only [hσ]
    rw [this]
    exact hrel b
  have key := card_le_of_semilinear d d' (fun b => Matrix.isDiag_diagonal _)
    (fun b => Matrix.isDiag_diagonal _) σ A hA (θ : B → B) θ.surjective hΘ
    (fun b => ((χ b : Kˣ) : K) ^ e) (fun b => (((twist θ (e * 2 ^ j) χ) b : Kˣ) : K)) (by
      intro b
      rw [twist_apply, hθ3 b, hσ, ← pow_mul]
      simp)
  unfold mult
  have h1 : (Finset.univ.filter fun i : ι => (fun i => (f i).comp ιB) i = χ) =
      Finset.univ.filter fun i : ι => ∀ b, d b i i = ((χ b : Kˣ) : K) ^ e := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h b
      have := congrArg (fun φ : B →* Kˣ => ((φ b : Kˣ) : K)) h
      simp only [MonoidHom.comp_apply] at this
      simp [d, this]
    · intro h
      refine char_pow_inj hB5 he ?_
      ext b
      have := h b
      simp only [d, Matrix.diagonal_apply_eq] at this
      simp [MonoidHom.pow_apply, this]
  have h2 : (Finset.univ.filter fun i : ι =>
      (fun i => (f i).comp ιB) i = twist θ (e * 2 ^ j) χ) =
      Finset.univ.filter fun i : ι => ∀ b, d' b i i = (((twist θ (e * 2 ^ j) χ) b : Kˣ) : K) := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h b
      have := congrArg (fun φ : B →* Kˣ => ((φ b : Kˣ) : K)) h
      simpa [d', diagOf] using this
    · intro h
      ext b
      simpa [d', diagOf] using h b
  rw [h1, h2]
  exact key

omit [Finite K] [CharP K 2] in
theorem isDiag_of_commute (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E)
    (hinj : Function.Injective fun i => (f i).comp ιB) (A : Matrix ι ι K)
    (h : ∀ b : B, A * diagOf f (ιB b) = diagOf f (ιB b) * A) : A.IsDiag := by
  intro i k hik
  by_contra hne
  have hdist : (f i).comp ιB ≠ (f k).comp ιB := fun hh => hik (hinj hh)
  obtain ⟨b, hb⟩ : ∃ b : B, f i (ιB b) ≠ f k (ιB b) := by
    by_contra hall
    push Not at hall
    exact hdist (MonoidHom.ext fun b => hall b)
  have h1 := congrFun (congrFun (h b) i) k
  simp only [diagOf, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : A i k * (((f k (ιB b) : Kˣ) : K) - ((f i (ιB b) : Kˣ) : K)) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact hne h3
  · exact hb (Units.ext (sub_eq_zero.1 h3).symm)

omit [Finite K] [CharP K 2] in
theorem diag_vec_mem_span (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E)
    (hinj : Function.Injective fun i => (f i).comp ιB) (e₀ : E) :
    (fun i => ((f i e₀ : Kˣ) : K)) ∈
      Submodule.span K (Set.range fun b : B => fun i => ((f i (ιB b) : Kˣ) : K)) := by
  let v : B → (ι → K) := fun b i => ((f i (ιB b) : Kˣ) : K)
  let u : ι → K := fun i => ((f i e₀ : Kˣ) : K)
  by_contra hu
  obtain ⟨l, hlu, hl⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu inferInstance
  set a : ι → K := fun i => l (fun j => if i = j then 1 else 0) with ha
  have hlv : ∀ w : ι → K, l w = ∑ i, a i * w i := fun w => by
    rw [LinearMap.pi_apply_eq_sum_univ l w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hsum : ∀ b : B, ∑ i, a i * v b i = 0 := fun b => by
    rw [← hlv]
    have : l (v b) ∈ (Submodule.span K (Set.range v)).map l :=
      ⟨v b, Submodule.subset_span ⟨b, rfl⟩, rfl⟩
    rw [hl] at this
    exact this
  have hli : LinearIndependent K fun i => ((((Units.coeHom K).comp
      ((f i).comp ιB)) : B →* K) : B → K) := by
    refine (linearIndependent_monoidHom B K).comp
      (fun i => (Units.coeHom K).comp ((f i).comp ιB)) ?_
    intro i k hik
    apply hinj
    ext b
    have := congrArg (fun φ : B →* K => φ b) hik
    exact this
  have hall : ∀ i, a i = 0 := by
    refine Fintype.linearIndependent_iff.1 hli a ?_
    funext b
    simpa [v] using hsum b
  apply hlu
  rw [hlv]
  simp [hall]

omit [Finite K] [CharP K 2] in
theorem diag_mem_span (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E)
    (hinj : Function.Injective fun i => (f i).comp ιB) (e₀ : E) :
    diagOf f e₀ ∈ Submodule.span K (Set.range fun b : B => diagOf f (ιB b)) := by
  have hu := diag_vec_mem_span f ιB hinj e₀
  have := Submodule.mem_map_of_mem (f := Matrix.diagonalLinearMap ι K K) hu
  rw [Submodule.map_span, ← Set.range_comp] at this
  exact this

omit [Finite K] [CharP K 2] in
theorem diag_core_II (f : ι → (E →* Kˣ)) {B : Type*} [Group B] (ιB : B →* E)
    (hE5 : ∀ x : E, x ^ 5 = 1)
    (hinj : Function.Injective fun i => (f i).comp ιB) (j e : ℕ)
    (hm : (e * 2 ^ j) % 5 = 1) (A : Matrix ι ι K)
    (hrel : ∀ b : B, A * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f (ιB b) * A) (e₀ : E) :
    A * Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K) ^ e) ^ 2 ^ j) = diagOf f e₀ * A := by
  have hpow : ∀ (x : E) (i : ι), (((f i x : Kˣ) : K) ^ e) ^ 2 ^ j = ((f i x : Kˣ) : K) := by
    intro x i
    have h5 : ((f i x : Kˣ) : K) ^ 5 = 1 := by
      have := congrArg (fun y : Kˣ => (y : K))
        (show (f i x) ^ 5 = 1 by rw [← map_pow, hE5 x, map_one])
      simpa using this
    rw [← pow_mul, pow_eq_pow_mod _ h5, hm, pow_one]
  have hdiagfun : ∀ x : E, Matrix.diagonal (fun i => (((f i x : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f x := fun x => by simp only [hpow, diagOf]
  have hB : ∀ b : B, A * diagOf f (ιB b) = diagOf f (ιB b) * A := fun b => by
    have := hrel b
    rwa [hdiagfun] at this
  have hdiag := isDiag_of_commute f ιB hinj A hB
  rw [hdiagfun, ← hdiag.diagonal_diag]
  simp only [diagOf, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

omit [CharP K 2] in
theorem not_dvd_five_mul (j e : ℕ) (he : e = 1 ∨ e = 4) : ¬ 5 ∣ e * 2 ^ j := by
  have h5 : Nat.Prime 5 := by norm_num
  intro h
  rcases h5.dvd_mul.1 h with h | h
  · rcases he with rfl | rfl <;> omega
  · have := h5.dvd_of_dvd_pow h
    omega

theorem weights_of_relation (f : Fin 4 → (E →* Kˣ)) {B : Type*} [CommGroup B] [Finite B]
    (ιB : B →* E) (hB25 : Nat.card B = 25) (hB5 : ∀ b : B, b ^ 5 = 1)
    (hfaith : ∀ b : B, (∀ i, f i (ιB b) = 1) → b = 1) (θ : MulAut B) (hθ3 : θ ^ 3 = 1)
    (hθ1 : θ ≠ 1) (j e : ℕ) (he : e = 1 ∨ e = 4) (A : Matrix (Fin 4) (Fin 4) K)
    (hA : IsUnit A)
    (hrel : ∀ b : B, A * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e) ^ 2 ^ j) =
      diagOf f (ιB (θ b)) * A) :
    (e * 2 ^ j) % 5 = 1 ∧ Function.Injective (fun i => (f i).comp ιB) ∧
      ∃ χ₀ : B →* Kˣ, χ₀ ≠ 1 ∧ χ₀ ∈ Set.range (fun i => (f i).comp ιB) ∧
        twist θ (e * 2 ^ j) χ₀ ∈ Set.range (fun i => (f i).comp ιB) ∧
        twist θ (e * 2 ^ j) (twist θ (e * 2 ^ j) χ₀) ∈ Set.range (fun i => (f i).comp ιB) := by
  have hnorm : ∀ b, b * θ b * θ (θ b) = 1 := norm_eq_one_of_order_three hB25 θ hθ3 hθ1
  have hθ3' : ∀ b, θ (θ (θ b)) = b := theta_cube θ hnorm
  have hm : ¬ 5 ∣ e * 2 ^ j := not_dvd_five_mul j e he
  have he5 : ¬ 5 ∣ e := fun h => hm (h.mul_right _)
  have hf1 : ∃ i, (f i).comp ιB ≠ 1 := by
    have : Nontrivial B := (Finite.one_lt_card_iff_nontrivial).1 (by rw [hB25]; norm_num)
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    by_contra hall
    push Not at hall
    exact hb (hfaith b fun i => by
      have := congrArg (fun φ : B →* Kˣ => φ b) (hall i)
      simpa using this)
  have H := mult_le_twist f ιB hB5 θ hθ3' j e he5 A hA hrel
  exact weight_lemma hB5 θ hnorm (fun i => (f i).comp ιB) (by simp) (e * 2 ^ j) hm hf1 H

omit [CharP K 2] in
theorem twist_refl_eq_pow {B X : Type*} [CommGroup B] [CommGroup X] (m : ℕ) (χ : B →* X) :
    twist (MulEquiv.refl B) m χ = χ ^ m := by
  ext b
  simp [twist_apply, MonoidHom.pow_apply]

theorem fixes_of_relation (f : Fin 4 → (E →* Kˣ)) {B : Type*} [CommGroup B] [Finite B]
    (ιB : B →* E) (hB5 : ∀ b : B, b ^ 5 = 1) (hE5 : ∀ x : E, x ^ 5 = 1) (θ : MulAut B)
    (hnorm : ∀ b, b * θ b * θ (θ b) = 1) (m : ℕ) (hm : ¬ 5 ∣ m)
    (hinj : Function.Injective fun i => (f i).comp ιB) {χ₀ : B →* Kˣ} (hχ₀ : χ₀ ≠ 1)
    (h0 : χ₀ ∈ Set.range (fun i => (f i).comp ιB))
    (h1 : twist θ m χ₀ ∈ Set.range (fun i => (f i).comp ιB))
    (h2 : twist θ m (twist θ m χ₀) ∈ Set.range (fun i => (f i).comp ιB))
    (l e' : ℕ) (he' : e' = 1 ∨ e' = 4) (A' : Matrix (Fin 4) (Fin 4) K) (hA' : IsUnit A')
    (hrel : ∀ b : B, A' * Matrix.diagonal (fun i => (((f i (ιB b) : Kˣ) : K) ^ e') ^ 2 ^ l) =
      diagOf f (ιB b) * A') (e₀ : E) :
    A' * Matrix.diagonal (fun i => (((f i e₀ : Kˣ) : K) ^ e') ^ 2 ^ l) = diagOf f e₀ * A' := by
  have hm' : ¬ 5 ∣ e' * 2 ^ l := not_dvd_five_mul l e' he'
  have he5 : ¬ 5 ∣ e' := fun h => hm' (h.mul_right _)
  have H := mult_le_twist f ιB hB5 (MulEquiv.refl B) (fun b => rfl) l e' he5 A' hA' hrel
  have hH' : ∀ χ : B →* Kˣ, mult (fun i => (f i).comp ιB) χ ≤
      mult (fun i => (f i).comp ιB) (χ ^ (e' * 2 ^ l)) := fun χ => by
    have := H χ
    rwa [twist_refl_eq_pow] at this
  have hscalar := scalar_lemma hB5 θ hnorm (fun i => (f i).comp ιB) (Fintype.card_fin 4) m hm hχ₀
    h0 h1 h2 (e' * 2 ^ l) hm' hH'
  exact diag_core_II f ιB hE5 hinj l e' hscalar A' hrel e₀

end Core

end CFSG.RankThree.PartOne.AUTSL
