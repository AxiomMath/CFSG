module

public import Certificates.Data.Kernel.Tower.Search

public section

namespace Certificates.KernelTower

@[expose] noncomputable def chunkB (p : Nat → Bool) (q : Nat) : Bool :=
  allFrom (Nat.mul 512 q) 512 p

theorem allB_true_iff {n : Nat} {p : Nat → Bool} : allB n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ n ih =>
    change (p n && allB n p) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h2 k h
      · rw [h]
        exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem allB_of_chunks {p : Nat → Bool} {m : Nat} (h : ∀ q < m, chunkB p q = true) :
    allB (512 * m) p = true := by
  rw [allB_true_iff]
  intro k hk
  have hc : allB 512 (fun i => p (Nat.add (Nat.mul 512 (k / 512)) i)) = true :=
    h (k / 512) (by omega)
  have hq : p (Nat.add (Nat.mul 512 (k / 512)) (k % 512)) = true :=
    allB_true_iff.1 hc (k % 512) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul 512 (k / 512)) (k % 512) = k := Nat.div_add_mod k 512
  rw [e] at hq
  exact hq

end Certificates.KernelTower
