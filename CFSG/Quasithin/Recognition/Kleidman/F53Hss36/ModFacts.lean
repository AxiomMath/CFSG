module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs.FixedPointCount

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Assembly CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

variable {G : Type*} [Group G]

@[expose] def conjPermOf {K : Subgroup G} {d : G} (hd : ∀ x ∈ K, d * x * d⁻¹ ∈ K)
    (hdi : ∀ x ∈ K, d⁻¹ * x * d⁻¹⁻¹ ∈ K) : Equiv.Perm K where
  toFun x := ⟨d * x * d⁻¹, hd x x.2⟩
  invFun x := ⟨d⁻¹ * x * d⁻¹⁻¹, hdi x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])

theorem conjPermOf_apply_val {K : Subgroup G} {d : G} (hd : ∀ x ∈ K, d * x * d⁻¹ ∈ K)
    (hdi : ∀ x ∈ K, d⁻¹ * x * d⁻¹⁻¹ ∈ K) (x : K) :
    ((conjPermOf hd hdi x : K) : G) = d * x * d⁻¹ := rfl

theorem conjPermOf_pow_apply_val {K : Subgroup G} {d : G} (hd : ∀ x ∈ K, d * x * d⁻¹ ∈ K)
    (hdi : ∀ x ∈ K, d⁻¹ * x * d⁻¹⁻¹ ∈ K) (n : ℕ) (x : K) :
    (((conjPermOf hd hdi) ^ n) x : G) = d ^ n * x * (d ^ n)⁻¹ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, conjPermOf_apply_val]
    group

theorem conjPermOf_pow_three {K : Subgroup G} {d : G} (hd : ∀ x ∈ K, d * x * d⁻¹ ∈ K)
    (hdi : ∀ x ∈ K, d⁻¹ * x * d⁻¹⁻¹ ∈ K) (hd3 : d ^ 3 = 1) :
    (conjPermOf hd hdi) ^ 3 = 1 := by
  refine Equiv.ext fun x => Subtype.ext ?_
  rw [conjPermOf_pow_apply_val, hd3]
  simp

end CFSG.Quasithin.Kleidman.F53Hss36

end
