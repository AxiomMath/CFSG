module

public import Mathlib.FieldTheory.Finite.Basic
import TauCeti.FieldTheory.Finite.FrobeniusFixed

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem w183b2_pow_card_mem {k : Type} [Field k] (F : Subfield k) [Finite F] (x : k) :
    x ^ Nat.card F = x ↔ x ∈ F := by
  rw [TauCeti.FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem w183b2_frob_descent {k : Type} [Field k] [CharP k 2] {U : Type} [AddCommGroup U]
    [Module k U] {n : ℕ} (b : Module.Basis (Fin n) k U) (F : Subfield k) [Finite F]
    (S : Set (Module.End k U)) (hspan : Submodule.span k S = ⊤)
    (hSF : ∀ s ∈ S, ∀ i j, LinearMap.toMatrix b b s i j ∈ F)
    (a : Module.End k U) (ha : a * a = 1) (haS : ∀ s ∈ S, ∃ s' ∈ S, a * s = s' * a) :
    ∀ i j, LinearMap.toMatrix b b a i j ∈ F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  have hmF : Nat.card F = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  let φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k :=
    RingHom.mapMatrix (iterateFrobenius k 2 (m : ℕ))
  have hfix : ∀ M : Matrix (Fin n) (Fin n) k, (∀ i j, M i j ∈ F) → φ M = M := by
    intro M hM
    ext i j
    change M i j ^ 2 ^ (m : ℕ) = M i j
    rw [← hmF]
    exact (w183b2_pow_card_mem F (M i j)).mpr (hM i j)
  let T : (U →ₗ[k] U) ≃ₐ[k] Matrix (Fin n) (Fin n) k := LinearMap.toMatrixAlgEquiv b
  change ∀ i j : Fin n, T a i j ∈ F
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact fun i => Fin.elim0 i
  have hA : T a * T a = 1 := by rw [← map_mul, ha, map_one]
  have hMspan : Submodule.span k (T '' S) = ⊤ := by
    have h := Submodule.map_span
      (f := (T : (U →ₗ[k] U) →ₗ[k] Matrix (Fin n) (Fin n) k)) (s := S)
    rw [hspan] at h
    have htop : (⊤ : Submodule k (U →ₗ[k] U)).map
        (T : (U →ₗ[k] U) →ₗ[k] Matrix (Fin n) (Fin n) k) = ⊤ := by
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr T.surjective
    rw [htop] at h
    exact h.symm
  have hcomm_s : ∀ s ∈ S, T s * (T a * φ (T a)) = (T a * φ (T a)) * T s := by
    intro s hs
    obtain ⟨s', hs', hss'⟩ := haS s hs
    have hM : T a * T s = T s' * T a := by rw [← map_mul, hss', map_mul]
    have hY : T s' = T a * T s * T a := by
      rw [hM, Matrix.mul_assoc, hA, Matrix.mul_one]
    have hPY : T a * T s' = T s * T a := by
      rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.one_mul]
    have hφ : φ (T a) * T s = T s' * φ (T a) := by
      have h := congrArg φ hM
      simp only [map_mul] at h
      rw [hfix (T s) (hSF s hs), hfix (T s') (hSF s' hs')] at h
      exact h
    calc T s * (T a * φ (T a))
        = (T s * T a) * φ (T a) := by rw [Matrix.mul_assoc]
      _ = (T a * T s') * φ (T a) := by rw [← hPY]
      _ = T a * (T s' * φ (T a)) := by rw [Matrix.mul_assoc]
      _ = T a * (φ (T a) * T s) := by rw [← hφ]
      _ = (T a * φ (T a)) * T s := by rw [Matrix.mul_assoc]
  let K : Submodule k (Matrix (Fin n) (Fin n) k) :=
    { carrier := {X | X * (T a * φ (T a)) = (T a * φ (T a)) * X}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        show (x + y) * (T a * φ (T a)) = (T a * φ (T a)) * (x + y)
        rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
      smul_mem' := by
        intro r x hx
        show (r • x) * (T a * φ (T a)) = (T a * φ (T a)) * (r • x)
        rw [Matrix.smul_mul, Matrix.mul_smul, hx] }
  have hKtop : (⊤ : Submodule k (Matrix (Fin n) (Fin n) k)) ≤ K := by
    rw [← hMspan]
    refine Submodule.span_le.mpr ?_
    rintro X ⟨s, hs, rfl⟩
    exact hcomm_s s hs
  have hCscalar : (T a * φ (T a)) ∈ Set.range (Matrix.scalar (Fin n)) := by
    rw [Matrix.mem_range_scalar_iff_commute_single']
    intro i j
    exact hKtop Submodule.mem_top
  obtain ⟨r, hr⟩ := hCscalar
  have hC : T a * φ (T a) = r • 1 := by
    rw [← hr, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  have hφA : φ (T a) = r • T a := by
    calc φ (T a) = 1 * φ (T a) := (Matrix.one_mul _).symm
      _ = (T a * T a) * φ (T a) := by rw [hA]
      _ = T a * (T a * φ (T a)) := by rw [Matrix.mul_assoc]
      _ = T a * (r • 1) := by rw [hC]
      _ = r • T a := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hQQ : φ (T a) * φ (T a) = 1 := by rw [← map_mul, hA, map_one]
  have hsq : φ (T a) * φ (T a) = (r * r) • (1 : Matrix (Fin n) (Fin n) k) := by
    rw [hφA]
    calc (r • T a) * (r • T a) = r • (T a * (r • T a)) := by rw [Matrix.smul_mul]
      _ = r • (r • (T a * T a)) := by rw [Matrix.mul_smul]
      _ = (r * r) • (T a * T a) := by rw [smul_smul]
      _ = (r * r) • 1 := by rw [hA]
  have hrrequiv : (r * r) • (1 : Matrix (Fin n) (Fin n) k) = 1 := hsq.symm.trans hQQ
  have hrrmul : r * r = 1 := by
    have h := congrFun (congrFun hrrequiv ⟨0, hnpos⟩) ⟨0, hnpos⟩
    simpa using h
  have hr1 : r = 1 := by
    have h : r ^ 2 = (1 : k) ^ 2 := by simpa [pow_two] using hrrmul
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp h) with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  have hφP : φ (T a) = T a := by rw [hφA, hr1, one_smul]
  intro i j
  have hentry : T a i j ^ 2 ^ (m : ℕ) = T a i j := by
    have h := congrFun (congrFun hφP i) j
    change T a i j ^ 2 ^ (m : ℕ) = T a i j at h
    exact h
  rw [← hmF] at hentry
  exact (w183b2_pow_card_mem F (T a i j)).mp hentry

end CFSG.LocalAnalysis.WeakClosure81

end
