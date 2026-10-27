module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieCartanAux3

public section

namespace CFSG.StandardType

open Finset Module CFSG.Open
open scoped IsMulCommutative

variable {G : Type} [Group G] {p N : ℕ} {Bs : Subgroup G}

@[expose] noncomputable def ggNSLiePI2_simpleSwap (N : ℕ) (i : Fin (N - 1)) : Equiv.Perm (Fin N) :=
  Equiv.swap ⟨i.1, by omega⟩ ⟨i.1 + 1, by omega⟩

lemma ggNSLiePI2_swap_comm_of_ne {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b := by
  apply Equiv.Perm.Disjoint.commute
  apply Equiv.Perm.disjoint_swap_swap
  rw [List.nodup_cons, List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [List.mem_cons, not_or, hab, hac, had]
  · simp [List.mem_cons, not_or, hbc, hbd]
  · simp [List.mem_cons, hcd]
  · simp [List.nodup_cons]

lemma ggNSLiePI2_swap_braid_of_ne {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c := by
  have h1 : Equiv.swap a b * Equiv.swap b c * Equiv.swap a b = Equiv.swap a c := by
    rw [show Equiv.swap a b = Equiv.swap b a from Equiv.swap_comm a b]
    rw [show Equiv.swap b c = Equiv.swap c b from Equiv.swap_comm b c]
    exact Equiv.swap_mul_swap_mul_swap (x := c) (y := b) (z := a) hbc.symm hac.symm
  have h2 : Equiv.swap b c * Equiv.swap a b * Equiv.swap b c = Equiv.swap a c := by
    rw [Equiv.swap_mul_swap_mul_swap (x := a) (y := b) (z := c) hab hac]
    exact Equiv.swap_comm c a
  rw [h1, h2]

lemma ggNSLiePI2_simpleSwap_comm (N : ℕ) (i j : Fin (N - 1))
    (hij : (i : ℕ) ≠ (j : ℕ)) (hij1 : (i : ℕ) + 1 ≠ (j : ℕ))
    (hi1j : (i : ℕ) ≠ (j : ℕ) + 1) :
    ggNSLiePI2_simpleSwap N i * ggNSLiePI2_simpleSwap N j =
      ggNSLiePI2_simpleSwap N j * ggNSLiePI2_simpleSwap N i := by
  apply ggNSLiePI2_swap_comm_of_ne
  · intro h; exact Nat.succ_ne_self _ (congrArg (fun x : Fin N => x.val) h).symm
  · intro h; exact Nat.succ_ne_self _ (congrArg (fun x : Fin N => x.val) h).symm
  · intro h; exact hij (by simpa using congrArg Fin.val h)
  · intro h; exact hi1j (congrArg (fun x : Fin N => x.val) h)
  · intro h; exact hij1 (congrArg Fin.val h)
  · intro h; exact hij (Nat.succ.inj (congrArg Fin.val h))

lemma ggNSLiePI2_simpleSwap_braid (N : ℕ) (i : Fin (N - 1)) (hi : (i : ℕ) + 1 < N - 1) :
    ggNSLiePI2_simpleSwap N i * ggNSLiePI2_simpleSwap N ⟨i.1 + 1, hi⟩ *
      ggNSLiePI2_simpleSwap N i =
    ggNSLiePI2_simpleSwap N ⟨i.1 + 1, hi⟩ * ggNSLiePI2_simpleSwap N i *
      ggNSLiePI2_simpleSwap N ⟨i.1 + 1, hi⟩ := by
  apply ggNSLiePI2_swap_braid_of_ne
  · intro h; exact Nat.succ_ne_self _ (congrArg (fun x : Fin N => x.val) h).symm
  · intro h; exact Nat.succ_ne_self _ (congrArg (fun x : Fin N => x.val) h).symm
  · intro h
    exact (by omega : (i : ℕ) ≠ (i : ℕ) + 2) (congrArg Fin.val h)

lemma ggNSLiePI2_simpleSwap_ne (N : ℕ) (i j : Fin (N - 1))
    (hij : (i : ℕ) ≠ (j : ℕ)) (hij1 : (i : ℕ) + 1 ≠ (j : ℕ))
    (hi1j : (i : ℕ) ≠ (j : ℕ) + 1) :
    ggNSLiePI2_simpleSwap N i ≠ ggNSLiePI2_simpleSwap N j := by
  intro heq
  have happ := congrArg (fun σ : Equiv.Perm (Fin N) => σ ⟨i.1, by omega⟩) heq
  have happ' : Equiv.swap (⟨i.1, by omega⟩ : Fin N) (⟨i.1 + 1, by omega⟩ : Fin N)
        ⟨i.1, by omega⟩ =
      Equiv.swap (⟨j.1, by omega⟩ : Fin N) (⟨j.1 + 1, by omega⟩ : Fin N)
        ⟨i.1, by omega⟩ := happ
  rw [Equiv.swap_apply_left] at happ'
  rw [Equiv.swap_apply_of_ne_of_ne] at happ'
  · exact Nat.succ_ne_self i.1 (congrArg (fun x : Fin N => x.val) happ')
  · intro h; exact hij (congrArg (fun x : Fin N => x.val) h)
  · intro h; exact hi1j (congrArg (fun x : Fin N => x.val) h)

lemma ggNSLiePI2_simpleSwap_ne_self (N : ℕ) (i : Fin (N - 1)) :
    (⟨i.1, by omega⟩ : Fin N) ≠ ⟨i.1 + 1, by omega⟩ := by
  intro h; exact Nat.succ_ne_self _ (congrArg Fin.val h).symm

lemma ggNSLiePI2_simpleSwap_ne_adj (N : ℕ) (i : Fin (N - 1)) (hi : (i : ℕ) + 1 < N - 1) :
    ggNSLiePI2_simpleSwap N ⟨i.1 + 1, hi⟩ ≠ ggNSLiePI2_simpleSwap N i := by
  intro heq
  have happ := congrArg (fun σ : Equiv.Perm (Fin N) => σ ⟨i.1, by omega⟩) heq
  have h1 : (ggNSLiePI2_simpleSwap N ⟨i.1 + 1, hi⟩) ⟨i.1, by omega⟩ = ⟨i.1, by omega⟩ := by
    change Equiv.swap (⟨i.1 + 1, by omega⟩ : Fin N) (⟨i.1 + 2, by omega⟩ : Fin N)
      ⟨i.1, by omega⟩ = ⟨i.1, by omega⟩
    exact Equiv.swap_apply_of_ne_of_ne
      (by intro h; have h' := congrArg Fin.val h; simp only [Fin.val_mk] at h'; omega)
      (by intro h; have h' := congrArg Fin.val h; simp only [Fin.val_mk] at h'; omega)
  have h2 : (ggNSLiePI2_simpleSwap N i) ⟨i.1, by omega⟩ = ⟨i.1 + 1, by omega⟩ := by
    change Equiv.swap (⟨i.1, by omega⟩ : Fin N) (⟨i.1 + 1, by omega⟩ : Fin N)
      ⟨i.1, by omega⟩ = ⟨i.1 + 1, by omega⟩
    exact Equiv.swap_apply_left _ _
  rw [h1, h2] at happ
  exact (by omega : (i : ℕ) ≠ (i : ℕ) + 1) (congrArg (fun x : Fin N => x.val) happ)

end CFSG.StandardType

end
