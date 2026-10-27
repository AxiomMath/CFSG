module

public import CFSG.Monster.B.Final.Basic
public import CFSG.Monster.B.Pinned.Primes.Program

public section

namespace CFSG.Monster.B.Pinned

open Bin Primes.Native CFSG.Blueprint

@[expose] noncomputable def wordB
    (w : String) : NativeSporadic.B := wordG bA₁ bA₂ w.toList

theorem bMat_wordB
    (w : String) : bMat (wordB w) = wordG genA₁ genA₂ w.toList := by
  rw [wordB, map_wordG, bMat_bA₁, bMat_bA₂]

theorem orderOf_of_prime {g : NativeSporadic.B} {p : ℕ} (hp : p.Prime) (h : g ^ p = 1 ∧ g ≠ 1) :
    orderOf g = p :=
  haveI : Fact p.Prime := ⟨hp⟩
  orderOf_eq_prime h.1 h.2

theorem orderOf_bMat (g : NativeSporadic.B) : orderOf (bMat g) = orderOf g :=
  orderOf_injective bMat bMat_injective g

end CFSG.Monster.B.Pinned
