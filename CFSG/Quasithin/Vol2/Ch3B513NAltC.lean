module

public import CFSG.Quasithin.Background.B3ThreeGen

public section

namespace CFSG.Quasithin.B513N

open CFSG.Quasithin.B3

@[expose] def a0 (n : ℕ) (hn : 4 ≤ n) : LG n :=
  ⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by simp [Fin.ext_iff]), Equiv.Perm.sign_swap (by simp [Fin.ext_iff])]
    rfl⟩

theorem a0_sq (n : ℕ) (hn : 4 ≤ n) : a0 n hn ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  show (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ * Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩)
    ^ 2 = 1
  ext i
  simp only [pow_two, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Equiv.Perm.one_apply]
  split_ifs <;> simp_all [Fin.ext_iff]

theorem actM_a0_xor {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    ∀ m < 2 ^ n, actM n (tab (a0 n (by omega)).1) m ^^^ m ∈ [0, 3, 12, 15] := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem actM_a0_seventeen {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    actM n (tab (a0 n (by omega)).1) 17 ^^^ 17 = 3 := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem actM_a0_one {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    actM n (tab (a0 n (by omega)).1) 1 ^^^ 1 = 3 := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem popPar_seventeen {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) : popPar n 17 = true := by
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem inWk_seventeen {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {k : Mod}
    (hk : k = Mod.u0 ∨ k = Mod.ut0) : inWk n k 17 = true := by
  rcases hk with rfl | rfl <;> exact popPar_seventeen hn

theorem act_a0_mul_inv_mem {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (k : Mod)
    (v : Mod.V n k) :
    Mod.act n k (a0 n (by omega)).1 v * v⁻¹ ∈
      ({toV n k 0, toV n k 3, toV n k 12, toV n k 15} : Set (Mod.V n k)) := by
  obtain ⟨m, hm, hmW, rfl⟩ := toV_surj k v
  rw [toV_ratio _ hmW]
  have h := actM_a0_xor hn m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> rw [h] <;> simp

theorem card_le_four_of_mem {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) (k : Mod)
    (R : Subgroup (Mod.V n k))
    (hR : ∀ x ∈ R, ∃ v, x = Mod.act n k (a0 n (by omega)).1 v * v⁻¹) : Nat.card R ≤ 4 := by
  classical
  have hsub : (R : Set (Mod.V n k)) ⊆ {toV n k 0, toV n k 3, toV n k 12, toV n k 15} := by
    intro x hx
    obtain ⟨v, rfl⟩ := hR x hx
    exact act_a0_mul_inv_mem hn k v
  calc Nat.card R = Nat.card (R : Set (Mod.V n k)) := rfl
    _ ≤ Nat.card ({toV n k 0, toV n k 3, toV n k 12, toV n k 15} : Set (Mod.V n k)) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ ≤ 4 := by
        rw [Nat.card_coe_set_eq]
        refine (Set.ncard_insert_le _ _).trans ?_
        refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
        refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
        rw [Set.ncard_singleton]

theorem d0_a0_eq {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) {k : Mod}
    (hk : k = Mod.u0 ∨ k = Mod.ut0) :
    d0 n k (a0 n (by omega)) =
      Mod.act n k (a0 n (by omega)).1 (toV n k 17) * (toV n k 17)⁻¹ := by
  rw [toV_ratio _ (inWk_seventeen hn hk), actM_a0_seventeen hn]
  show toV n k (actM n (tab (a0 n (by omega)).1) 1 ^^^ 1) = _
  rw [actM_a0_one hn]

end CFSG.Quasithin.B513N
