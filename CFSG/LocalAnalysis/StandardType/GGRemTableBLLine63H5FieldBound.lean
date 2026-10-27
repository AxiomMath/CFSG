module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5FieldE

public section

namespace CFSG.StandardType.Line63.H5

open Polynomial Module

theorem card_le_nine_of_fieldType {K : Type} [Field K] [Finite K]
    (hω : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1)
    {M : GL (Fin 6) K} {l : Kˣ} (hM3 : M ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) l)
    (hl : ∀ c : Kˣ, c ^ 3 ≠ l)
    {S : Subgroup (GL (Fin 6) K)} (hMS : M ∈ S) (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (_hscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ S)
    (hpow : ∀ Y ∈ S, ∃ k : Kˣ, Y ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) k) :
    Nat.card S ≤ 9 * Nat.card Kˣ := by
  classical
  obtain ⟨ω, hω3, hω1⟩ := hω
  have hωp : IsPrimitiveRoot (ω : K) 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := IsPrimitiveRoot.orderOf ω
    rw [orderOf_eq_prime hω3 hω1] at h
    exact IsPrimitiveRoot.coe_units_iff.mpr h
  have hc : ∀ d : K, d ^ 3 ≠ (l : K) := fun d hd => by
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hd
      exact l.ne_zero hd.symm
    exact hl (Units.mk0 d hd0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd]))
  have hirr : Irreducible (X ^ 3 - C (l : K) : K[X]) := by
    have hdeg : (X ^ 3 - C (l : K) : K[X]).natDegree = 3 := natDegree_X_pow_sub_C
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp)
      fun μ hμ => ?_
    rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hμ
    exact hc μ hμ
  set x : Module.End K (Fin 6 → K) := Matrix.toLin' (M : Matrix (Fin 6) (Fin 6) K) with hx
  have hM3' : (M : Matrix (Fin 6) (Fin 6) K) ^ 3 = Matrix.scalar (Fin 6) (l : K) := by
    rw [← Units.val_pow_eq_pow_val, hM3, Matrix.GeneralLinearGroup.coe_scalar]
  have hxl : aeval x (X ^ 3 - C (l : K) : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hx, ← Matrix.toLin'_pow, hM3', sub_eq_zero]
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Module.algebraMap_end_apply, Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  have hscinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 6) : Kˣ →* GL (Fin 6) K) := by
    intro c c' h
    have h1 : Matrix.scalar (Fin 6) (c : K) = Matrix.scalar (Fin 6) (c' : K) := by
      have := congrArg Units.val h
      simpa only [Matrix.GeneralLinearGroup.coe_scalar] using this
    exact Units.ext (Matrix.scalar_inj.mp h1)
  have hex : ∀ Y : S, ∃ k : Kˣ,
      (Y : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) k :=
    fun Y => hpow Y.1 Y.2
  choose cube hcube using hex
  let c : S →* Kˣ :=
    { toFun := cube
      map_one' := by
        apply hscinj
        have h := hcube 1
        rw [Subgroup.coe_one, one_pow] at h
        rw [map_one]
        exact h.symm
      map_mul' := fun Y Y' => by
        apply hscinj
        rw [map_mul, ← hcube Y, ← hcube Y', ← hcube (Y * Y'), Subgroup.coe_mul]
        exact Commute.mul_pow (hcomm Y.1 Y.2 Y'.1 Y'.2) 3 }
  rw [← Subgroup.card_ker_mul_card_range c]
  refine Nat.mul_le_mul ?_ (Subgroup.card_le_card_group _)
  have hker : ∀ i : c.ker, ((i.1 : S) : GL (Fin 6) K) ^ 3 = 1 := by
    intro i
    have h1 : cube i.1 = 1 := MonoidHom.mem_ker.mp i.2
    rw [hcube i.1, h1, map_one]
  have hcm : ∀ A B : Matrix (Fin 6) (Fin 6) K, A * B = B * A →
      Commute (Matrix.toLin' A) (Matrix.toLin' B) := fun A B h => by
    change Matrix.toLin' A * Matrix.toLin' B = Matrix.toLin' B * Matrix.toLin' A
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
      ← Matrix.toLin'_mul, h]
  have hgl : ∀ A B : GL (Fin 6) K, A * B = B * A →
      Commute (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) K))
        (Matrix.toLin' (B : Matrix (Fin 6) (Fin 6) K)) := fun A B h =>
    hcm _ _ (by rw [← Units.val_mul, ← Units.val_mul, h])
  refine card_le_nine_of_commute_pow_three_eq_one hirr hxl (Module.finrank_fin_fun K) hωp
    (fun i : c.ker => Matrix.toLin' (((i.1 : S) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
    ?_ (fun i j => hgl _ _ (hcomm _ i.1.2 _ j.1.2)) (fun i => hgl _ _ (hcomm _ i.1.2 _ hMS))
    (fun i => ?_)
  · intro i j hij
    have h1 := Matrix.toLin'.injective hij
    exact Subtype.ext (Subtype.ext (Units.ext h1))
  · rw [← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hker i, Units.val_one,
      Matrix.toLin'_one]
    rfl

end CFSG.StandardType.Line63.H5

end
