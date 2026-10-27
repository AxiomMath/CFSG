module

public import CFSG.GroupTheory.OddAbelianInvolutionDecomp

@[expose] public section

namespace CFSG

theorem exists_fixed_mul_fixed_of_fixedPointFree_mul
    {A : Type*} [CommGroup A] [Finite A] (hodd : Odd (Nat.card A))
    (τ t : MulAut A) (hτ2 : τ * τ = 1) (ht2 : t * t = 1)
    (hcomm : τ * t = t * τ) (hfree : ∀ y : A, τ y = y → y = 1) (y : A) :
    ∃ a b : A, (τ * t) a = a ∧ t b = b ∧ y = a * b := by
  let toAdd : MulAut A → AddAut (Additive A) :=
    fun u => (AddAutAdditive A).symm (Additive.ofMul u)
  have htoAdd_mul : ∀ u v : MulAut A, toAdd (u * v) = toAdd u + toAdd v := by
    intro u v
    simpa [toAdd] using
      (AddAutAdditive A).symm.map_add (Additive.ofMul u) (Additive.ofMul v)
  have htoAdd_one : toAdd 1 = 0 := by
    simpa [toAdd] using (AddAutAdditive A).symm.map_zero
  have happly : ∀ (u : MulAut A) (x : Additive A),
      toAdd u x = Additive.ofMul (u (Additive.toMul x)) := fun _ _ => rfl
  have hτ2' : toAdd τ + toAdd τ = 0 := by
    rw [← htoAdd_mul, hτ2, htoAdd_one]
  have ht2' : toAdd t + toAdd t = 0 := by
    rw [← htoAdd_mul, ht2, htoAdd_one]
  have hcomm' : toAdd τ + toAdd t = toAdd t + toAdd τ := by
    rw [← htoAdd_mul, ← htoAdd_mul, hcomm]
  have hfree' : ∀ x : Additive A, toAdd τ x = x → x = 0 := by
    intro x hx
    have hx' : τ (Additive.toMul x) = Additive.toMul x := by
      have h := congrArg Additive.toMul hx
      rw [happly] at h
      simpa using h
    have hx0 : Additive.toMul x = 1 := hfree (Additive.toMul x) hx'
    simpa using congrArg Additive.ofMul hx0
  haveI : Finite (Additive A) := ‹Finite A›
  obtain ⟨a, b, ha, hb, hy⟩ :=
    exists_fixed_mul_fixed_of_fixedPointFree (A := Additive A) hodd (toAdd τ) (toAdd t)
      hτ2' ht2' hcomm' hfree' (Additive.ofMul y)
  refine ⟨Additive.toMul a, Additive.toMul b, ?_, ?_, ?_⟩
  · have h := congrArg Additive.toMul ha
    rw [← htoAdd_mul, happly] at h
    simpa using h
  · have h := congrArg Additive.toMul hb
    rw [happly] at h
    simpa using h
  · have h := congrArg Additive.toMul hy
    simpa using h

end CFSG
