module

public import CFSG.Certificates.Kernel.BabyMonster.DyStabBlk
public import CFSG.Certificates.Kernel.BabyMonster.DyStabDefs

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat

theorem rowsNe_add (C : List (List Nat)) (X lo : Nat) :
    ∀ len, rowsNe C X (lo + len) = andB (rowsNe C X lo) (rowsNeR C X lo len)
  | 0 => by
    rw [Nat.add_zero]
    cases rowsNe C X lo <;> rfl
  | len + 1 => by
    have e1 : rowsNe C X (lo + len + 1) = andB (rowsNe C X (lo + len))
        (andB (Nat.blt (recOf C (lo + len)) dyFail) (notB (Nat.beq (recOf C (lo + len)) X))) := rfl
    have e2 : rowsNeR C X lo (len + 1) = andB (rowsNeR C X lo len)
        (andB (Nat.blt (recOf C (lo + len)) dyFail) (notB (Nat.beq (recOf C (lo + len)) X))) := rfl
    rw [← Nat.add_assoc, e1, e2, rowsNe_add C X lo len]
    cases rowsNe C X lo <;> cases rowsNeR C X lo len <;> rfl

theorem rowsNe_blocks {C : List (List Nat)} {X : Nat} :
    ∀ k, (∀ b < k, rowsNeB C X b = true) → rowsNe C X (64 * k) = true
  | 0, _ => rfl
  | k + 1, h => by
    have e : 64 * (k + 1) = 64 * k + 64 := by omega
    rw [e, rowsNe_add, rowsNe_blocks k fun b hb => h b (by omega)]
    exact h k (by omega)

theorem rowsNe_4371 {C : List (List Nat)} {X : Nat} (h : ∀ b < 68, rowsNeB C X b = true)
    (ht : rowsNeR C X 4352 19 = true) : rowsNe C X 4371 = true := by
  have h1 : rowsNe C X 4352 = true := rowsNe_blocks 68 h
  have e := rowsNe_add C X 4352 19
  rw [h1, ht] at e
  exact e

end CertificateChecks.KernelBM.Dy

end
