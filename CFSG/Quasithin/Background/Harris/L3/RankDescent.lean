module

public import CFSG.RankThree.Classical.SemilinearFixedBasis
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.G11.Harris.L3

open Matrix

section Field

variable {F : Type*} [Field F] [Finite F] {k : ℕ}

theorem frob_frob_eq {σ : F ≃+* F} (hF : Nat.card F = 2 ^ (2 * k)) (hσ : ∀ x, σ x = x ^ 2 ^ k)
    (x : F) : σ (σ x) = x := by
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ (2 * k) := by rw [← hF, Nat.card_eq_fintype_card]
  rw [hσ, hσ, ← pow_mul, ← pow_add, ← two_mul, ← hF', FiniteField.pow_card]

theorem card_fixed_le (hk : 1 ≤ k) {σ : F ≃+* F} (hσ : ∀ x, σ x = x ^ 2 ^ k) :
    Nat.card {x : F // σ x = x} ≤ 2 ^ k := by
  classical
  have hk' : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq F hk'
  have hp : (Polynomial.X ^ 2 ^ k - Polynomial.X : Polynomial F) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hmem : ∀ x : {x : F // σ x = x},
      x.1 ∈ (Polynomial.X ^ 2 ^ k - Polynomial.X : Polynomial F).roots.toFinset := by
    intro x
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hσ, x.2, sub_self]
  calc Nat.card {x : F // σ x = x}
      ≤ Nat.card (Polynomial.X ^ 2 ^ k - Polynomial.X : Polynomial F).roots.toFinset :=
        Nat.card_le_card_of_injective (fun x => ⟨x.1, hmem x⟩) (fun a b h => Subtype.ext
          (by simpa using h))
    _ = Finset.card (Polynomial.X ^ 2 ^ k - Polynomial.X : Polynomial F).roots.toFinset := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Multiset.card (Polynomial.X ^ 2 ^ k - Polynomial.X : Polynomial F).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (Polynomial.X ^ 2 ^ k - Polynomial.X : Polynomial F).natDegree :=
        Polynomial.card_roots' _
    _ = 2 ^ k := hdeg

theorem orderOf_frob (hk : 1 ≤ k) {σ : F ≃+* F} (hF : Nat.card F = 2 ^ (2 * k))
    (hσ : ∀ x, σ x = x ^ 2 ^ k) : orderOf σ = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · refine RingEquiv.ext fun x => ?_
    show σ (σ x) = x
    exact frob_frob_eq hF hσ x
  · intro h1
    have hfix : ∀ x : F, σ x = x := fun x => by rw [h1]; rfl
    have h2 : Nat.card F ≤ 2 ^ k := by
      calc Nat.card F = Nat.card {x : F // σ x = x} :=
            Nat.card_congr (Equiv.subtypeUnivEquiv hfix).symm
        _ ≤ 2 ^ k := card_fixed_le hk hσ
    have h3 : 2 ^ k < 2 ^ (2 * k) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end Field

section Hilbert

variable {F : Type} [Field F] [Finite F] {k : ℕ}

theorem exists_fixed_matrix (hk : 1 ≤ k) (hF : Nat.card F = 2 ^ (2 * k)) {σ : F ≃+* F}
    (hσ : ∀ x, σ x = x ^ 2 ^ k) (A : Matrix (Fin 3) (Fin 3) F) (hA : A * A.map σ = 1) :
    ∃ B : Matrix (Fin 3) (Fin 3) F, IsUnit B.det ∧ A * B.map σ = B := by
  have hord := orderOf_frob hk hF hσ
  have hTT : ∀ v : Fin 3 → F, A *ᵥ (σ ∘ (A *ᵥ (σ ∘ v))) = v := by
    intro v
    have h1 : σ ∘ (A *ᵥ (σ ∘ v)) = (A.map σ) *ᵥ (σ ∘ σ ∘ v) :=
      funext fun i => RingHom.map_mulVec σ.toRingHom A (σ ∘ v) i
    have h2 : σ ∘ σ ∘ v = v := funext fun i => frob_frob_eq hF hσ (v i)
    rw [h1, h2, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  let T : (Fin 3 → F) ≃+ (Fin 3 → F) :=
    { toFun := fun v => A *ᵥ (σ ∘ v)
      invFun := fun v => A *ᵥ (σ ∘ v)
      left_inv := hTT
      right_inv := hTT
      map_add' := fun v w => by
        have : σ ∘ (v + w) = σ ∘ v + σ ∘ w := funext fun i => map_add σ (v i) (w i)
        simp only [this, Matrix.mulVec_add] }
  have hT : ∀ v, T v = A *ᵥ (σ ∘ v) := fun v => rfl
  have ha : ∀ (c : F) (v : Fin 3 → F), T (c • v) = σ c • T v := fun c v => by
    rw [hT, hT]
    have : σ ∘ (c • v) = σ c • (σ ∘ v) := funext fun i => map_mul σ c (v i)
    rw [this, Matrix.mulVec_smul]
  have hah : ∀ v, (⇑T)^[2] v = v := fun v => hTT v
  obtain ⟨-, -, -, -, b, hb, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis Nat.prime_two (by omega) hF σ hord
      (Module.finrank_fin_fun F) T ha hah
  refine ⟨(Pi.basisFun F (Fin 3)).toMatrix b, ?_, ?_⟩
  · rw [← Module.Basis.det_apply]
    exact (Pi.basisFun F (Fin 3)).isUnit_det b
  · ext i j
    have h1 := congrFun (hb j) i
    rw [hT] at h1
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, ← h1, Matrix.mul_apply, Matrix.mulVec,
      dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl

end Hilbert

end CFSG.Quasithin.G11.Harris.L3
