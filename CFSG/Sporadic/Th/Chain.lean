
module

public import CFSG.Sporadic.Th.ChainBase1

public import CFSG.Sporadic.Th.Index

public section

namespace CFSG.Sporadic.Th

open Native Pointwise

section TreeOrbit

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

section Data

variable {g₁ g₂ : G} {m r : ℕ} {pts lk : ℕ → ℕ} {pl : Table}

end Data

end TreeOrbit

section Reps

variable {c : ℕ} (hC : CertFacts c)
include hC

theorem eq_one_of_fix
    (g : J) (hg : ∀ j < 124, idx nX g j = j) : g = 1 :=
  eq_one_of_idx_fix hC.orbit hC.delta (nX_ge hC) hg

theorem eq_one_of_idx_id
    (g : J) (hg : ∀ i < nX, idx nX g i = i) : g = 1 :=
  eq_one_of_fix hC g fun j hj => hg j (lt_of_lt_of_le hj (nX_ge hC))

theorem a_sq :
    a ^ 2 = 1 := eq_one_of_idx_id hC _ (idx_sq_of_invoOK (rep_a hC) hC.aInvo)

theorem b_cube :
    b ^ 3 = 1 := eq_one_of_idx_id hC _ (idx_cube_of_order3OK (rep_b hC) hC.bOrd3)

theorem x_sq : xJ ^ 2 = 1 :=
  eq_one_of_idx_id hC _ (idx_sq_of_invoOK (rep_x hC) hC.tables.xInvo)

theorem y_cube : yJ ^ 3 = 1 :=
  eq_one_of_idx_id hC _ (idx_cube_of_order3OK (rep_y hC) hC.tables.yOrd3)

theorem eq_of_residue
    {g r : J} (h : ∀ j < 124, idx nX (r⁻¹ * g) j = j) : g = r := by
  have := eq_one_of_fix hC _ h
  rw [inv_mul_eq_one] at this
  exact this.symm

end Reps

end CFSG.Sporadic.Th
