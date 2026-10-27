module

public import CFSG.RankThree.PartOne.KFCL.L4Torus
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.RankThree.PartOne.KFCL.L4

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def conjSL (A : GL (Fin 4) K) : SL(4, K) ≃* SL(4, K) where
  toFun x := ⟨(A : Matrix (Fin 4) (Fin 4) K) * x.1 * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K), by
    rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.det_one]⟩
  invFun x := ⟨((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * x.1 * (A : Matrix (Fin 4) (Fin 4) K), by
    rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.det_one]⟩
  left_inv x := Subtype.ext (by
    have h1 : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (A : Matrix (Fin 4) (Fin 4) K) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    show ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((A : Matrix (Fin 4) (Fin 4) K) * x.1 * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) *
        (A : Matrix (Fin 4) (Fin 4) K) = x.1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one])
  right_inv x := Subtype.ext (by
    have h1 : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (A : Matrix (Fin 4) (Fin 4) K) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    show (A : Matrix (Fin 4) (Fin 4) K) *
      (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * x.1 * (A : Matrix (Fin 4) (Fin 4) K)) *
        ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = x.1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one])
  map_mul' x y := Subtype.ext (by
    have h1 : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    show (A : Matrix (Fin 4) (Fin 4) K) * (x.1 * y.1) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * x.1 * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((A : Matrix (Fin 4) (Fin 4) K) * y.1 * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    calc (A : Matrix (Fin 4) (Fin 4) K) * (x.1 * y.1) * ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = (A : Matrix (Fin 4) (Fin 4) K) * x.1 *
            (((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K)) * y.1 *
              ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
          rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc])

theorem card_torus_le (p : ℕ) (hp : 0 < p) : Nat.card (torus p K) ≤ p ^ 3 := by
  classical
  let R : Finset K := Polynomial.nthRootsFinset p (1 : K)
  have hR : R.card ≤ p := by
    have := Polynomial.card_nthRoots p (1 : K)
    exact (Multiset.toFinset_card_le _).trans this
  let f : torus p K → (Fin 3 → R) := fun g i =>
    ⟨g.1.1 (Fin.castSucc i) (Fin.castSucc i), by
      rw [Polynomial.mem_nthRootsFinset hp]
      exact torus_pow_apply g.2 _⟩
  have hf : Function.Injective f := by
    intro g g' h
    have h0 : g.1.1 0 0 = g'.1.1 0 0 := congrArg Subtype.val (congrFun h 0)
    have h1 : g.1.1 1 1 = g'.1.1 1 1 := congrArg Subtype.val (congrFun h 1)
    have h2 : g.1.1 2 2 = g'.1.1 2 2 := congrArg Subtype.val (congrFun h 2)
    have hp1 := torus_prod g.2
    have hp2 := torus_prod g'.2
    rw [Fin.prod_univ_four] at hp1 hp2
    have h3 : g.1.1 3 3 = g'.1.1 3 3 := by
      have key : ∀ {a0 a1 a2 a3 b3 : K}, a0 * a1 * a2 * a3 = 1 → a0 * a1 * a2 * b3 = 1 → a3 = b3 := by
        intro a0 a1 a2 a3 b3 h h'
        have hne : a0 * a1 * a2 ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at h
          exact zero_ne_one h
        exact mul_left_cancel₀ hne (h.trans h'.symm)
      refine key hp1 ?_
      simpa only [← h0, ← h1, ← h2] using hp2
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simpa using ‹_›
    · rw [torus_apply_ne g.2 hij, torus_apply_ne g'.2 hij]
  calc Nat.card (torus p K) ≤ Nat.card (Fin 3 → R) := Nat.card_le_card_of_injective f hf
    _ = Nat.card R ^ 3 := by rw [Nat.card_fun]; simp
    _ ≤ p ^ 3 := by
      apply Nat.pow_le_pow_left
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact hR

theorem exists_frame [Finite K] {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (E₀ : Subgroup (SL(4, K))) (hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x)
    (hpow : ∀ x ∈ E₀, x ^ p = 1) (hcard : Nat.card E₀ = p ^ 3) :
    ∃ A : GL (Fin 4) K, E₀.map (conjSL A).toMonoidHom = torus p K := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A, hA⟩ := CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one hζ E₀ hcomm hpow
  refine ⟨A, ?_⟩
  have hle : E₀.map (conjSL A).toMonoidHom ≤ torus p K := by
    rintro _ ⟨x, hx, rfl⟩
    show conjSL A x ∈ torus p K
    have hoff : ∀ i j, i ≠ j → (conjSL A x).1 i j = 0 := fun i j hij => hA x hx i j hij
    refine ⟨fun i => (conjSL A x).1 i i, ?_, fun i => ?_⟩
    · ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [hoff i j hij, diagonal_apply_ne _ hij]
    · have hxp : (conjSL A x) ^ p = 1 := by
        rw [← map_pow, hpow x hx, map_one]
      have h1 := congrArg (fun g : SL(4, K) => g.1 i i) hxp
      simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h1
      have hd : (conjSL A x).1 = diagonal (fun i => (conjSL A x).1 i i) := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp
        · rw [hoff a b hab, diagonal_apply_ne _ hab]
      rw [hd, diagonal_pow] at h1
      simpa using h1
  have hcard1 : Nat.card (E₀.map (conjSL A).toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (conjSL A).injective]
    exact hcard
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1]; exact card_torus_le p hp.pos)

end CFSG.RankThree.PartOne.KFCL.L4
