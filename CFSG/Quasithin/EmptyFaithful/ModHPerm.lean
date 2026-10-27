module

public import CFSG.Quasithin.EmptyFaithful.ModGPerm

public section

namespace CFSG.Quasithin.ModH

open CFSG.Quasithin.ModG

@[expose] def pkn (n : ℕ) (f : Equiv.Perm (Fin n)) : ℕ := enc (List.ofFn fun i : Fin n => (f i).val + 1)

@[expose] def compn (n a b : ℕ) : ℕ := enc ((List.range n).map (ci a b))

@[expose] def kIdn (n : ℕ) : ℕ := enc ((List.range n).map (· + 1))

theorem digits_lt_n {n : ℕ} (hn : n ≤ 31) (f : Equiv.Perm (Fin n)) :
    ∀ d ∈ List.ofFn (fun i : Fin n => (f i).val + 1), d < 32 := by
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hd
  have := (f i).isLt
  omega

theorem dg_pkn {n : ℕ} (hn : n ≤ 31) (f : Equiv.Perm (Fin n)) (j : ℕ) (hj : j < n) :
    dg (pkn n f) j = (f ⟨j, hj⟩).val + 1 := by
  rw [pkn, dg_enc _ (digits_lt_n hn f), List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]

theorem ci_pkn {n : ℕ} (hn : n ≤ 31) (f g : Equiv.Perm (Fin n)) (i : ℕ) (hi : i < n) :
    ci (pkn n f) (pkn n g) i = ((f * g) ⟨i, hi⟩).val + 1 := by
  have h1 := dg_pkn hn g i hi
  have h2 : Nat.sub (dg (pkn n g) i) 1 = (g ⟨i, hi⟩).val := by
    rw [h1]
    rfl
  rw [ci, h2, dg_pkn hn f (g ⟨i, hi⟩).val (g ⟨i, hi⟩).isLt]
  rfl

theorem pkn_mul {n : ℕ} (hn : n ≤ 31) (f g : Equiv.Perm (Fin n)) :
    pkn n (f * g) = compn n (pkn n f) (pkn n g) := by
  have h1 : List.ofFn (fun i : Fin n => ((f * g) i).val + 1) =
      (List.range n).map (ci (pkn n f) (pkn n g)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hi : i < n := by simpa using h1
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      exact (ci_pkn hn f g i hi).symm
  rw [pkn, h1, compn]

theorem pkn_injective {n : ℕ} (hn : n ≤ 31) : Function.Injective (pkn n) := by
  intro f g h
  ext i
  have h1 := dg_pkn hn f i.val i.isLt
  have h2 := dg_pkn hn g i.val i.isLt
  rw [h] at h1
  have := h1.symm.trans h2
  simpa using this

theorem pkn_one (n : ℕ) : pkn n (1 : Equiv.Perm (Fin n)) = kIdn n := by
  have h1 : List.ofFn (fun i : Fin n => ((1 : Equiv.Perm (Fin n)) i).val + 1) =
      (List.range n).map (· + 1) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  rw [pkn, h1, kIdn]

end CFSG.Quasithin.ModH
