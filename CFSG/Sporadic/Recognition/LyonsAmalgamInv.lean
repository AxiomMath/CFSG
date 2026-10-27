module

public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.Th

open Native

theorem getElem!_set!' {α : Type*} [Inhabited α] (a : Array α) (k r : ℕ) (v : α)
    (hr : r < a.size) : (a.set! k v)[r]! = if k = r then v else a[r]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds k v) r (by simpa using hr),
    Array.getElem_setIfInBounds hr, getElem!_pos a r hr]

theorem foldl_set_inv {n : ℕ} (P : Table) (hlt : ∀ i < n, ap P i < n)
    (hinj : ∀ i < n, ∀ i' < n, ap P i = ap P i' → i = i') :
    ∀ (m s : ℕ), s + m ≤ n → ∀ a : Array UInt32, a.size = n →
      ((List.range' s m).foldl (fun r i => r.set! (ap P i) (UInt32.ofNat i)) a).size = n ∧
      (∀ i, s ≤ i → i < s + m →
        ((List.range' s m).foldl (fun r i => r.set! (ap P i) (UInt32.ofNat i)) a)[ap P i]! =
          UInt32.ofNat i) ∧
      (∀ j, j < n → (∀ i, s ≤ i → i < s + m → ap P i ≠ j) →
        ((List.range' s m).foldl (fun r i => r.set! (ap P i) (UInt32.ofNat i)) a)[j]! = a[j]!) := by
  intro m
  induction m with
  | zero =>
    intro s _ a ha
    exact ⟨ha, fun i h1 h2 => by omega, fun j _ _ => rfl⟩
  | succ m ih =>
    intro s hsm a ha
    rw [List.range'_succ, List.foldl_cons]
    set a' := a.set! (ap P s) (UInt32.ofNat s) with ha'
    have hsize' : a'.size = n := by rw [ha', Array.size_set!, ha]
    obtain ⟨h1, h2, h3⟩ := ih (s + 1) (by omega) a' hsize'
    refine ⟨h1, fun i hi1 hi2 => ?_, fun j hj hmiss => ?_⟩
    · by_cases his : i = s
      · subst his
        rw [h3 (ap P i) (hlt i (by omega)) (fun i' hi'1 hi'2 h => by
          have := hinj i (by omega) i' (by omega) h.symm
          omega)]
        rw [ha', getElem!_set!' _ _ _ _ (by rw [ha]; exact hlt i (by omega)), ite_eq_left rfl]
      · exact h2 i (by omega) (by omega)
    · rw [h3 j hj (fun i hi1 hi2 => hmiss i (by omega) (by omega)), ha',
        getElem!_set!' _ _ _ _ (by rw [ha]; exact hj), ite_eq_right (hmiss s le_rfl (by omega))]

theorem invT_eq_foldl (n : ℕ) (P : Table) :
    invT n P = (List.range' 0 n).foldl (fun r i => r.set! (ap P i) (UInt32.ofNat i))
      (Array.replicate n 0) := by
  unfold invT
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rfl

section Perm

variable {n : ℕ}

theorem rep_invT_of_rep (hn : n < 2 ^ 32) {P : Table} {g : Equiv.Perm (Fin n)} (hP : Rep n P g) :
    Rep n (invT n P) g⁻¹ := by
  have hlt : ∀ i < n, ap P i < n := fun i hi => by rw [hP i hi]; exact idx_lt g hi
  have hinj : ∀ i < n, ∀ i' < n, ap P i = ap P i' → i = i' := by
    intro i hi i' hi' h
    rw [hP i hi, hP i' hi'] at h
    rw [idx_of_lt g hi, idx_of_lt g hi'] at h
    have := g.injective (Fin.ext h : g ⟨i, hi⟩ = g ⟨i', hi'⟩)
    exact congrArg Fin.val this
  obtain ⟨hsize, hhit, -⟩ := foldl_set_inv P hlt hinj n 0 (by omega) (Array.replicate n 0)
    (by simp)
  intro j hj
  have hi : idx n g⁻¹ j < n := idx_lt _ hj
  have hpi : ap P (idx n g⁻¹ j) = j := by rw [hP _ hi, idx_idx_inv]
  have := hhit (idx n g⁻¹ j) (by omega) (by omega)
  rw [hpi] at this
  rw [← invT_eq_foldl] at this
  unfold ap
  rw [this, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (hi.trans hn)]

theorem invOK_invT_of_rep (hn : n < 2 ^ 32) {P : Table} {g : Equiv.Perm (Fin n)}
    (hP : Rep n P g) : invOK n P (invT n P) = true := by
  have hR := rep_invT_of_rep hn hP
  rw [invOK, allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, hR _ (idx_lt g hi), idx_inv_idx]

end Perm

end CFSG.Sporadic.Th
