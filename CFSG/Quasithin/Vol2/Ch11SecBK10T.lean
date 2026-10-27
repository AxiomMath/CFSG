module

public import CFSG.Quasithin.Vol2.Ch11SecBK10I

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem mem_inner_of_two_pow {X : Type} [Group X] [Finite X] (hout : Odd (Nat.card (Outer X)))
    {s : MulAut X} {k : ℕ} (hs : s ^ 2 ^ k = 1) : s ∈ inner X := by
  have : Finite (Outer X) := inferInstance
  set π := QuotientGroup.mk' (inner X)
  have h1 : orderOf (π s) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hs, map_one])
  have h2 : orderOf (π s) ∣ Nat.card (Outer X) := orderOf_dvd_natCard (π s)
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Outer X)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hout)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

namespace Sz

open Matrix

variable {K : Type} [Field K]

theorem exists_diag_eq_of_map_eq_conj {n : ℕ} {M : Matrix (Fin n) (Fin n) K}
    (hM : M.BlockTriangular OrderDual.toDual) (σ : K ≃+* K) (g : GL (Fin n) K)
    (h : M.map σ = (g : Matrix (Fin n) (Fin n) K) * M * ((g⁻¹ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) (i : Fin n) : ∃ j, σ (M i i) = M j j := by
  have hT : ∀ c : K, (M - Matrix.scalar (Fin n) c).BlockTriangular OrderDual.toDual := fun c =>
    hM.sub (by rw [Matrix.scalar_apply]; exact blockTriangular_diagonal _)
  have hd : ∀ c : K, (M - Matrix.scalar (Fin n) c).det = ∏ j, (M j j - c) := fun c => by
    refine (Matrix.det_of_isLowerTriangular _ (hT c)).trans ?_
    simp [Matrix.scalar_apply]
  have h0 : (M - Matrix.scalar (Fin n) (M i i)).det = 0 := by
    rw [hd]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hconj : ∀ c : K, (M.map σ - Matrix.scalar (Fin n) c).det =
      (M - Matrix.scalar (Fin n) c).det := fun c => by
    have hc : (g : Matrix (Fin n) (Fin n) K) * Matrix.scalar (Fin n) c *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c := by
      rw [← (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).eq, Matrix.mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    have e : (g : Matrix (Fin n) (Fin n) K) * M * ((g⁻¹ : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - Matrix.scalar (Fin n) c = (g : Matrix (Fin n) (Fin n) K) *
          (M - Matrix.scalar (Fin n) c) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hc]
    rw [h, e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  have h1 : (M - Matrix.scalar (Fin n) (σ (M i i))).det = 0 := by
    rw [← hconj]
    have e : M.map σ - Matrix.scalar (Fin n) (σ (M i i)) =
        (σ : K →+* K).mapMatrix (M - Matrix.scalar (Fin n) (M i i)) := by
      rw [map_sub, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.scalar_apply,
        Matrix.scalar_apply, diagonal_map (map_zero _)]
      rfl
    rw [e, ← RingHom.map_det, h0, map_zero]
  rw [hd] at h1
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp h1
  exact ⟨j, (sub_eq_zero.mp hj).symm⟩

theorem apply_eq_of_sq {σ : K ≃+* K} (hσ : Odd (orderOf σ)) {x : K} (h : (σ ^ 2) x = x) :
    σ x = x := by
  obtain ⟨m, hm⟩ := hσ
  have h1 : σ = (σ ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf σ + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h1]
  exact L2.pow_apply_eq h _

theorem apply_eq_of_add_inv {σ : K ≃+* K} (hσ : Odd (orderOf σ)) {m : K} (hm : m ≠ 0)
    (h : σ (m + m⁻¹) = m + m⁻¹) : σ m = m := by
  have h1 : σ m = m ∨ σ m = m⁻¹ := by
    refine L2.eq_or_eq_inv_of_add_inv ((map_ne_zero σ).mpr hm) hm ?_
    rw [← map_inv₀, ← map_add, h]
  refine apply_eq_of_sq hσ ?_
  rw [sq, L2.ringAut_mul_apply]
  rcases h1 with e | e
  · rw [e, e]
  · rw [e, map_inv₀, e, inv_inv]

theorem eq_of_mem_four {σ : K ≃+* K} (hσ : Odd (orderOf σ)) {m₁ m₂ : K} (h₁ : m₁ ≠ 0)
    (h₂ : m₂ ≠ 0) (H₁ : σ m₁ = m₁ ∨ σ m₁ = m₂ ∨ σ m₁ = m₂⁻¹ ∨ σ m₁ = m₁⁻¹)
    (H₂ : σ m₂ = m₁ ∨ σ m₂ = m₂ ∨ σ m₂ = m₂⁻¹ ∨ σ m₂ = m₁⁻¹) : σ m₁ = m₁ ∧ σ m₂ = m₂ := by
  set A := m₁ + m₁⁻¹ with hA
  set B := m₂ + m₂⁻¹ with hB
  have hsum : ∀ m : K, σ (m + m⁻¹) = σ m + (σ m)⁻¹ := fun m => by rw [map_add, map_inv₀]
  have hAB : ∀ m : K, (σ m = m₁ ∨ σ m = m₂ ∨ σ m = m₂⁻¹ ∨ σ m = m₁⁻¹) →
      σ (m + m⁻¹) = A ∨ σ (m + m⁻¹) = B := by
    intro m hm
    rw [hsum]
    rcases hm with e | e | e | e <;> rw [e]
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr (by rw [inv_inv, add_comm])
    · exact Or.inl (by rw [inv_inv, add_comm])
  have hσA : σ A = A ∨ σ A = B := hAB m₁ (by
    rcases H₁ with e | e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr e)))
  have hσB : σ B = A ∨ σ B = B := hAB m₂ H₂
  have hA' : σ A = A := by
    refine apply_eq_of_sq hσ ?_
    rw [sq, L2.ringAut_mul_apply]
    rcases hσA with e | e
    · rw [e, e]
    · rcases hσB with e' | e'
      · rw [e, e']
      · have : A = B := σ.injective (e.trans e'.symm)
        rw [e, e']
        exact this.symm
  have hB' : σ B = B := by
    rcases hσB with e | e
    · have : B = A := σ.injective (e.trans hA'.symm)
      rw [e, this]
    · exact e
  exact ⟨apply_eq_of_add_inv hσ h₁ hA', apply_eq_of_add_inv hσ h₂ hB'⟩

theorem eq_one_of_fix_generator {σ : K ≃+* K} {l : Kˣ} (hl : ∀ x : Kˣ, x ∈ Subgroup.zpowers l)
    (h : σ (l : K) = l) : σ = 1 := by
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · rw [hx, map_zero]
    rfl
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hl (Units.mk0 x hx))
    have e : x = ((l ^ k : Kˣ) : K) := by rw [hk, Units.val_mk0]
    rw [e, Units.val_zpow_eq_zpow_val, map_zpow₀, h]
    rfl

end Sz

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
