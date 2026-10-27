module

public import Certificates.Data.A5GL42

public section

namespace Certificates.Asc82NormA6

open Certificates.A5GL42 (Mat4 ofCode)

@[expose] def beta (i : Fin 6) : ℕ := ![1, 2, 4, 8, 15, 0] i

@[expose] def spread (w : ℕ) : ℕ :=
  w % 2 + 16 * (w / 2 % 2) + 256 * (w / 4 % 2) + 4096 * (w / 8 % 2)

@[expose] def col (π : Equiv.Perm (Fin 6)) (i : Fin 6) : ℕ := beta (π i) ^^^ beta (π 5)

@[expose] def rhoCode (π : Equiv.Perm (Fin 6)) : ℕ :=
  spread (col π 0) + 2 * spread (col π 1) + 4 * spread (col π 2) + 8 * spread (col π 3)

@[expose] def rho (π : Equiv.Perm (Fin 6)) : Mat4 := ofCode (rhoCode π)

@[expose] def codesS0 : List ℕ :=
  (((Finset.univ : Finset (Equiv.Perm (Fin 6))).filter fun a => a.sign = 1).image
    rhoCode).sort (· ≤ ·)

@[expose] def sigma : Equiv.Perm (Fin 6) := List.formPerm [0, 1, 2]

@[expose] def tau : Equiv.Perm (Fin 6) := List.formPerm [1, 2, 3, 4, 5]

@[expose] def Rel {M : Type*} [Monoid M] (x y : M) : Prop :=
  x ^ 3 = 1 ∧ y ^ 5 = 1 ∧ (x * y ^ 4 * x ^ 2 * y) ^ 2 = 1 ∧ (x ^ 2 * y ^ 4) ^ 4 = 1 ∧
    (x * y * x * y ^ 4) ^ 3 = 1 ∧ (y * x ^ 2 * y ^ 4 * x ^ 2 * y) ^ 3 = 1

instance {M : Type*} [Monoid M] [DecidableEq M] (x y : M) : Decidable (Rel x y) := by
  unfold Rel; infer_instance

structure Facts : Prop where
  rho_one : rho 1 = 1
  rho_mul : ∀ p q : Equiv.Perm (Fin 6), rho (p * q) = rho p * rho q
  rho_ker : ∀ p : Equiv.Perm (Fin 6), rho p = 1 → p = 1
  sigma_even : sigma.sign = 1
  tau_even : tau.sign = 1
  rel : Rel sigma tau
  gen : ∀ a : Equiv.Perm (Fin 6), a.sign = 1 →
    a ∈ Subgroup.closure ({sigma, tau} : Set (Equiv.Perm (Fin 6)))
  classify : ∀ x y : Mat4, Rel x y → x ≠ 1 →
    ∃ c c' : Mat4, c * c' = 1 ∧ (∃ a : Equiv.Perm (Fin 6), a.sign = 1 ∧ rho a = c' * x * c) ∧
      ∃ b : Equiv.Perm (Fin 6), b.sign = 1 ∧ rho b = c' * y * c
  complete : ∀ g : Mat4, (∃ g' : Mat4, g * g' = 1) →
    (∀ a : Equiv.Perm (Fin 6), a.sign = 1 →
      ∃ a' : Equiv.Perm (Fin 6), a'.sign = 1 ∧ g * rho a = rho a' * g) →
    ∃ p : Equiv.Perm (Fin 6), rho p = g

end Certificates.Asc82NormA6
