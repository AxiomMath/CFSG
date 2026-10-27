module

public import CFSG.Quasithin.H13.Sp62S6Over
public import CFSG.Permutation.FinPackPow

public section

namespace CFSG.Quasithin.H13.A6K

open Equiv CFSG.Permutation.FinPack CFSG.Quasithin.H13.A6

theorem h16 : 6 ≤ 16 := by norm_num

@[expose] noncomputable def p1K (c : ℕ) : Bool :=
  Nat.beq (Nat.div (rd c 4) 2) 2 && Nat.beq (Nat.div (rd c 5) 2) 2

@[expose] noncomputable def p2K (c : ℕ) : Bool :=
  Nat.beq (Nat.div (rd c 0) 2) (Nat.div (rd c 1) 2) &&
    (Nat.beq (Nat.div (rd c 2) 2) (Nat.div (rd c 3) 2) &&
      Nat.beq (Nat.div (rd c 4) 2) (Nat.div (rd c 5) 2))

theorem p1K_iff (σ : Perm (Fin 6)) : p1K (enc σ) = true ↔ InP1 σ := by
  have e4 : rd (enc σ) 4 = σ 4 := rd_enc h16 σ 4
  have e5 : rd (enc σ) 5 = σ 5 := rd_enc h16 σ 5
  rw [p1K, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq, e4, e5]
  exact Iff.rfl

theorem blocks_iff (f : Fin 6 → ℕ) :
    (∀ i j : Fin 6, (i : ℕ) / 2 = (j : ℕ) / 2 → f i = f j) ↔ f 0 = f 1 ∧ f 2 = f 3 ∧ f 4 = f 5 := by
  constructor
  · intro H
    exact ⟨H 0 1 rfl, H 2 3 rfl, H 4 5 rfl⟩
  · rintro ⟨h1, h2, h3⟩ i j hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact h1 | exact h1.symm | exact h2 | exact h2.symm | exact h3 | exact h3.symm |
        (exfalso; revert hij; decide)

theorem p2K_iff (σ : Perm (Fin 6)) : p2K (enc σ) = true ↔ InP2 σ := by
  refine Iff.trans ?_ (blocks_iff (fun i => (σ i : ℕ) / 2)).symm
  have e0 : rd (enc σ) 0 = σ 0 := rd_enc h16 σ 0
  have e1 : rd (enc σ) 1 = σ 1 := rd_enc h16 σ 1
  have e2 : rd (enc σ) 2 = σ 2 := rd_enc h16 σ 2
  have e3 : rd (enc σ) 3 = σ 3 := rd_enc h16 σ 3
  have e4 : rd (enc σ) 4 = σ 4 := rd_enc h16 σ 4
  have e5 : rd (enc σ) 5 = σ 5 := rd_enc h16 σ 5
  simp only [p2K, Bool.and_eq_true, Nat.beq_eq]
  rw [e0, e1, e2, e3, e4, e5]
  exact Iff.rfl

end CFSG.Quasithin.H13.A6K
