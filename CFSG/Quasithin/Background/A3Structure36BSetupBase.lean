
module

public import CFSG.Quasithin.Background.A3Structure36BKernel

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

variable {X : Type} [Group X]

structure KernelSetup (X : Type) [Group X] (K : Subgroup X) : Prop where
  data : IsKernelData X K
  psl : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ IsPSL 2 r 1 (X ⧸ CFSG.solvableRadical X)
  sl2 : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧
    ∃ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod r), Function.Surjective φ ∧ φ.ker = K
  prime : ∀ p : ℕ, p.Prime → IsPi X p → ∃ D : PrimeData X p, D.K = K

theorem le_kernel_of_odd {K N : Subgroup X} (hK : IsKernelData X K)
    (hN : N ≤ CFSG.solvableRadical X) [Finite X] (hodd : Odd (Nat.card N)) : N ≤ K := by
  intro x hx
  obtain ⟨j, hj⟩ := hodd
  have h1 : x ^ Nat.card N = 1 := by
    have := pow_card_eq_one' (G := N) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  have h2 : x = (x ^ 2) ^ (j + 1) := by
    have : (x ^ 2) ^ (j + 1) = x ^ Nat.card N * x := by
      rw [hj, ← pow_mul, ← pow_succ]
      congr 1
    rw [this, h1, one_mul]
  rw [h2]
  exact pow_mem (hK.sq x (hN hx)) _

end CFSG.Quasithin.A36B
