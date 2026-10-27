module

public import CFSG.Quasithin.Background.E11Setup

public section

namespace CFSG.Quasithin

namespace G11

namespace E11

open scoped LinearAlgebra.Projectivization

theorem finrank_eq_mul_of_card {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N] [Finite M] [Finite N] {k : ℕ}
    (h : Nat.card M = Nat.card N ^ k) :
    Module.finrank (ZMod 2) M = k * Module.finrank (ZMod 2) N := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := N)
  rw [Nat.card_zmod] at h1 h2
  rw [h2, ← pow_mul] at h
  rw [h] at h1
  have := Nat.pow_right_injective (le_refl 2) h1
  rw [mul_comm] at this
  exact this.symm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

section Subspace

variable [Finite V] (hfix : fixedSpace H = ⊥)
  (I' : Submodule (HRing H) V) [IsSimpleModule (HRing H) I']

theorem le_iff_submodule_le_homInto (hiso : IsIsotypicOfType (HRing H) V I')
    (M : Submodule (HRing H) V) (J : Submodule (ZMod 2) V) (hJ : IrrPlus H J) :
    J ≤ M.restrictScalars (ZMod 2) ↔
      ((pointEquiv hfix I' hiso).symm ⟨J, hJ⟩).submodule ≤ homInto M := by
  set p := (pointEquiv hfix I' hiso).symm ⟨J, hJ⟩ with hp
  have hpJ : pointSub I' p = J := congrArg Subtype.val
    ((pointEquiv hfix I' hiso).apply_symm_apply ⟨J, hJ⟩)
  rw [← hpJ]
  clear_value p
  induction p using Projectivization.ind with
  | h φ hφ =>
    rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem,
      mem_homInto_iff_range_le]
    exact Submodule.restrictScalars_le (ZMod 2)

end Subspace

end E11

end G11

end CFSG.Quasithin
