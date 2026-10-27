module

public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.StandardType

private lemma ldim_exists_mulVec_ne_zero {n : ℕ} {K : Type} [Field K]
    {M : Matrix (Fin n) (Fin n) K} (hM : M ≠ 0) :
    ∃ u : Fin n → K, M.mulVec u ≠ 0 := by
  obtain ⟨p, q, hpq⟩ : ∃ p q : Fin n, M p q ≠ 0 := by
    by_contra h
    push Not at h
    exact hM (Matrix.ext (by simpa using h))
  refine ⟨Pi.single q 1, ?_⟩
  rw [Matrix.mulVec_single_one]
  intro h
  exact hpq (by simpa [Matrix.col_apply] using congrFun h p)

private lemma ldim_injective_sum {K : Type} [Field K] {a n : ℕ} {E : Type} [Field E]
    (ρ : Matrix (Fin a) (Fin a) E → Matrix (Fin n) (Fin n) K)
    (hmul : ∀ X Y, ρ (X * Y) = ρ X * ρ Y)
    (hzero : ρ 0 = 0)
    (u : Fin n → K) (k₀ : Fin a)
    (hw : (ρ (Matrix.single k₀ k₀ 1)).mulVec u ≠ 0)
    {y : Fin a → E}
    (hy : ∑ j, (ρ (Matrix.single j k₀ (y j))).mulVec u = 0) :
    y = 0 := by
  funext j'
  by_contra hne
  have h1 : (ρ (Matrix.single k₀ j' 1)).mulVec
      (∑ j, (ρ (Matrix.single j k₀ (y j))).mulVec u) = 0 := by
    rw [hy, Matrix.mulVec_zero]
  have h2 : (ρ (Matrix.single k₀ j' 1)).mulVec
      (∑ j, (ρ (Matrix.single j k₀ (y j))).mulVec u) =
      ∑ j, (ρ (Matrix.single k₀ j' 1) * ρ (Matrix.single j k₀ (y j))).mulVec u := by
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_mulVec u _ _
  have h3 : (∑ j, (ρ (Matrix.single k₀ j' 1) * ρ (Matrix.single j k₀ (y j))).mulVec u) =
      (ρ (Matrix.single k₀ k₀ (y j'))).mulVec u := by
    rw [Finset.sum_eq_single j']
    · rw [← hmul, Matrix.single_mul_single_same, one_mul]
    · intro j _ hjj
      rw [← hmul, Matrix.single_mul_single_of_ne (1 : E) k₀ j' j hjj.symm (y j), hzero,
        Matrix.zero_mulVec]
    · intro hj; exact absurd (Finset.mem_univ j') hj
  have hzero3 : (ρ (Matrix.single k₀ k₀ (y j'))).mulVec u = 0 := by
    rw [← h3, ← h2, h1]
  have h4 : (ρ (Matrix.single k₀ k₀ ((y j')⁻¹))).mulVec
      ((ρ (Matrix.single k₀ k₀ (y j'))).mulVec u) = 0 := by
    rw [hzero3, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, ← hmul, Matrix.single_mul_single_same, inv_mul_cancel₀ hne] at h4
  exact hw h4

theorem ggNbrLSideLin_dim {K : Type} [Field K] {r n : ℕ} {D : Fin r → Type} {d : Fin r → ℕ}
    [∀ i, Field (D i)] [∀ i, Algebra K (D i)] [∀ i, Finite (D i)]
    (Φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[K] Matrix (Fin n) (Fin n) K)
    (hΦ : Function.Injective Φ) (i : Fin r) :
    d i * Module.finrank K (D i) ≤ n := by
  classical
  by_cases hd : d i = 0
  · rw [hd, Nat.zero_mul]
    exact Nat.zero_le n
  have hsingle_ne :
      Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i
        (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) ≠ 0 := by
    intro h
    have hk : 0 < d i := Nat.pos_of_ne_zero hd
    let k : Fin (d i) := ⟨0, hk⟩
    have h1 := congrFun h i
    have h2 := congrFun (congrFun h1 k) k
    simpa using h2
  let ρ : Matrix (Fin (d i)) (Fin (d i)) (D i) → Matrix (Fin n) (Fin n) K :=
    fun X => Φ (Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i X)
  have hρ_add : ∀ X Y, ρ (X + Y) = ρ X + ρ Y := by
    intro X Y
    simp only [ρ, Pi.single_add, map_add]
  have hρ_smul : ∀ (c : K) (X : Matrix (Fin (d i)) (Fin (d i)) (D i)), ρ (c • X) = c • ρ X := by
    intro c X
    simp only [ρ, Pi.single_smul, map_smul]
  have hρ_mul : ∀ X Y, ρ (X * Y) = ρ X * ρ Y := by
    intro X Y
    simp only [ρ, Pi.single_mul, map_mul]
  have hρ_zero : ρ 0 = 0 := by
    simp only [ρ, Pi.single_zero, map_zero]
  have hρ_one_ne : ρ 1 ≠ 0 := by
    intro h
    exact hsingle_ne (hΦ (by simpa [ρ] using h))
  obtain ⟨u, hu⟩ := ldim_exists_mulVec_ne_zero hρ_one_ne
  have hsingle_sum :
      Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i
          (∑ k : Fin (d i), Matrix.single k k (1 : D i)) =
        ∑ k : Fin (d i),
          Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) (D j)) i
            (Matrix.single k k (1 : D i)) := by
    ext j p q
    by_cases hj : j = i
    · subst hj
      simp [Pi.single_apply, Finset.sum_apply]
    · simp [Pi.single_apply, Finset.sum_apply, hj]
  have hsum1 : ρ 1 = ∑ k : Fin (d i), ρ (Matrix.single k k 1) := by
    simp only [ρ]
    rw [← Matrix.sum_single_one (m := Fin (d i)) (α := D i)]
    rw [hsingle_sum, map_sum]
  have hsum_vec : (ρ 1).mulVec u = ∑ k, (ρ (Matrix.single k k 1)).mulVec u := by
    rw [hsum1]
    simpa using Matrix.sum_mulVec Finset.univ (fun k => ρ (Matrix.single k k 1)) u
  have hex : ∃ k : Fin (d i), (ρ (Matrix.single k k 1)).mulVec u ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    rw [hsum_vec]
    exact Finset.sum_eq_zero fun k _ => h k
  obtain ⟨k₀, hk₀⟩ := hex
  let T : (Fin (d i) → D i) →ₗ[K] (Fin n → K) :=
    { toFun := fun y => ∑ j : Fin (d i), (ρ (Matrix.single j k₀ (y j))).mulVec u
      map_add' := by
        intro x y
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.single_add, hρ_add, Matrix.add_mulVec]
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Matrix.smul_single, hρ_smul, Matrix.smul_mulVec] }
  have hinj : Function.Injective T := by
    intro x y hxy
    have h0 : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz : x - y = 0 := by
      apply ldim_injective_sum ρ hρ_mul hρ_zero u k₀ hk₀
      simpa [T, Pi.sub_apply] using h0
    exact sub_eq_zero.mp hz
  have hle := LinearMap.finrank_le_finrank_of_injective (f := T) hinj
  rw [Module.finrank_fintype_fun_eq_card] at hle
  haveI : Module.Finite K (D i) := Module.Finite.of_finite
  haveI : Module.Free K (D i) := Module.Free.of_divisionRing K (D i)
  rw [Module.finrank_pi_fintype] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  simpa using hle

end CFSG.StandardType

end
