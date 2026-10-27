module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem commSpace_top_eq_commSub (X : Subgroup (LGL 2 V)) :
    commSpace X ⊤ = commSub X := by
  unfold commSpace commSub
  congr 1
  ext w
  constructor
  · rintro ⟨x, hx, u, -, rfl⟩
    exact ⟨x, hx, u, rfl⟩
  · rintro ⟨x, hx, u, rfl⟩
    exact ⟨x, hx, u, trivial, rfl⟩

@[expose] def IsRegularOnNonzero (X : Subgroup (LGL 2 V)) (W : Submodule (ZMod 2) V) : Prop :=
  (∀ x ∈ X, ∀ w ∈ W, w ≠ 0 → x w = w → x = 1) ∧
  (∀ v ∈ W, v ≠ 0 → ∀ w ∈ W, w ≠ 0 → ∃ x ∈ X, x v = w)

theorem isCompl_fixSub_commSub_of_odd (X : Subgroup (LGL 2 V)) (hodd : Odd (Nat.card X)) :
    IsCompl (fixSub X) (commSub X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCompl_fixSub_commSub (p := 2) (Q := X) (Nat.coprime_two_left.mpr hodd)

def trivModSub (U : Submodule (ZMod 2) V) : Subgroup (LGL 2 V) where
  carrier := {a | ∀ v, a v - v ∈ U}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro a b ha hb v
    have h1 : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [h1]
    exact U.add_mem (ha (b v)) (hb v)
  inv_mem' := by
    intro a ha v
    have h2 : a⁻¹ v - v = - (a (a⁻¹ v) - a⁻¹ v) := by
      rw [apply_inv_apply' a v]; abel
    rw [h2]
    exact U.neg_mem (ha (a⁻¹ v))

theorem commSub_sup (A B : Subgroup (LGL 2 V)) :
    commSub (A ⊔ B) = commSub A ⊔ commSub B := by
  refine le_antisymm ?_ ?_
  · rw [commSub_le_iff]
    intro a ha v
    have hle : A ⊔ B ≤ trivModSub (commSub A ⊔ commSub B) := by
      refine sup_le ?_ ?_
      · intro a ha v
        exact Submodule.mem_sup_left (sub_mem_commSub A ha v)
      · intro b hb v
        exact Submodule.mem_sup_right (sub_mem_commSub B hb v)
    exact hle ha v
  · refine sup_le ?_ ?_
    · rw [commSub_le_iff]
      intro a ha v
      exact sub_mem_commSub (A ⊔ B) (Subgroup.mem_sup_left ha) v
    · rw [commSub_le_iff]
      intro b hb v
      exact sub_mem_commSub (A ⊔ B) (Subgroup.mem_sup_right hb) v

end CFSG.LocalAnalysis.WeakClosure81
