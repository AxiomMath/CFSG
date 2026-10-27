module

public import CFSG.Quasithin.EmptyFaithful.A38c6Defs
public import CFSG.Quasithin.Background.B3CaseB

public section

namespace CFSG.Quasithin.A38c6

open CFSG.Quasithin.A38c5.Fm

private theorem b3c_cj_eq (γ : P8) (X : Subgroup P8) : B3.cj γ X = cjP γ X := rfl

private theorem b3c_cjP_zpowers_swap (γ : P8) (a b : Fin 8) :
    cjP γ (Subgroup.zpowers (Equiv.swap a b)) = Subgroup.zpowers (Equiv.swap (γ a) (γ b)) := by
  unfold cjP
  rw [MonoidHom.map_zpowers, Equiv.swap_apply_apply]
  simp [MulAut.conj_apply]

private theorem b3c_exists_swap_lt_cjP {X : Subgroup P8} (γ : P8) {a b : Fin 8} (hab : a ≠ b)
    (hlt : Subgroup.zpowers (Equiv.swap a b) < X) :
    ∃ c d : Fin 8, c ≠ d ∧ Subgroup.zpowers (Equiv.swap c d) < cjP γ X :=
  ⟨γ a, γ b, fun h => hab (γ.injective h), by
    rw [← b3c_cjP_zpowers_swap]
    exact (Subgroup.map_lt_map_iff_of_injective (MulAut.conj γ).injective).2 hlt⟩

private theorem b3c_exists_perm (a b : Fin 8) (hab : a ≠ b) : ∃ γ : P8, γ 0 = a ∧ γ 1 = b := by
  refine ⟨Equiv.swap (Equiv.swap 0 a 1) b * Equiv.swap 0 a, ?_⟩
  revert a b
  decide

private theorem b3c_mem_zpowers_swap {a b : Fin 8} {g : P8}
    (hg : g ∈ Subgroup.zpowers (Equiv.swap a b)) : g = 1 ∨ g = Equiv.swap a b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have h2 : Equiv.swap a b ^ (2 : ℤ) = 1 := by rw [zpow_two, Equiv.swap_mul_self]
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

private theorem b3c_Am_one : B3.Am 8 1 = Subgroup.zpowers (Equiv.swap (0 : Fin 8) 1) := by
  unfold B3.Am
  rw [Subgroup.zpowers_eq_closure]
  congr 1
  ext g
  simp only [B3.gensAm, List.range_one, List.map_cons, List.map_nil, List.mem_singleton,
    Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro rfl; decide
  · rintro rfl; decide

private theorem b3c_swap01_mem_Am {m : ℕ} (hm : 1 ≤ m) :
    Equiv.swap (0 : Fin 8) 1 ∈ B3.Am 8 m := by
  have h : Equiv.swap (0 : Fin 8) 1 = B3.ti 8 0 := by decide
  rw [h]
  apply Subgroup.subset_closure
  simp only [B3.gensAm, List.mem_map, List.mem_range, Set.mem_ofPred_eq]
  exact ⟨0, by omega, rfl⟩

private theorem b3c_swap23_mem_Am {m : ℕ} (hm : 2 ≤ m) :
    Equiv.swap (2 : Fin 8) 3 ∈ B3.Am 8 m := by
  have h : Equiv.swap (2 : Fin 8) 3 = B3.ti 8 1 := by decide
  rw [h]
  apply Subgroup.subset_closure
  simp only [B3.gensAm, List.mem_map, List.mem_range, Set.mem_ofPred_eq]
  exact ⟨1, by omega, rfl⟩

private theorem b3c_swap23_not_mem :
    Equiv.swap (2 : Fin 8) 3 ∉ Subgroup.zpowers (Equiv.swap (0 : Fin 8) 1) := by
  intro h
  rcases b3c_mem_zpowers_swap h with h | h <;> revert h <;> decide

private theorem b3c_zpowers_lt_Am {m : ℕ} (hm : 2 ≤ m) (_hm4 : m ≤ 4) :
    Subgroup.zpowers (Equiv.swap (0 : Fin 8) 1) < B3.Am 8 m :=
  lt_of_le_of_ne (Subgroup.zpowers_le.2 (b3c_swap01_mem_Am (by omega)))
    (fun h => b3c_swap23_not_mem (h ▸ b3c_swap23_mem_Am hm))

open CFSG.Quasithin.B3 in
theorem zpowers_swap_mem_conjClass {a b : Fin 8} (hab : a ≠ b) :
    Subgroup.zpowers (Equiv.swap a b) ∈ B3.conjClass (B3.Am 8 1) := by
  obtain ⟨γ, hγ0, hγ1⟩ := b3c_exists_perm a b hab
  refine ⟨γ, ?_⟩
  rw [b3c_cj_eq, b3c_Am_one, b3c_cjP_zpowers_swap, hγ0, hγ1]

open CFSG.Quasithin.B3 in
theorem exists_swap_of_mem_conjClass_Am_one {A : Subgroup P8} (hA : A ∈ B3.conjClass (B3.Am 8 1)) :
    ∃ a b : Fin 8, a ≠ b ∧ A = Subgroup.zpowers (Equiv.swap a b) := by
  obtain ⟨γ, rfl⟩ := hA
  refine ⟨γ 0, γ 1, fun h => absurd (γ.injective h) (by decide), ?_⟩
  rw [b3c_cj_eq, b3c_Am_one, b3c_cjP_zpowers_swap]

open CFSG.Quasithin.B3 in
theorem exists_swap_lt_of_mem_conjClass_Am {m : ℕ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) {A : Subgroup P8}
    (hA : A ∈ B3.conjClass (B3.Am 8 m)) :
    ∃ a b : Fin 8, a ≠ b ∧ Subgroup.zpowers (Equiv.swap a b) < A := by
  obtain ⟨γ, rfl⟩ := hA
  rw [b3c_cj_eq]
  exact b3c_exists_swap_lt_cjP γ (by decide) (b3c_zpowers_lt_Am hm2 hm4)

private theorem b3c_swap45_mem_A0 : Equiv.swap (4 : Fin 8) 5 ∈ B3.A0 8 := by
  apply Subgroup.subset_closure
  show Equiv.swap (4 : Fin 8) 5 ∈ B3.gensA0 8
  decide

private theorem b3c_dt_mem_A0 : Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 ∈ B3.A0 8 := by
  apply Subgroup.subset_closure
  show Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 ∈ B3.gensA0 8
  decide

private theorem b3c_dt_not_mem :
    Equiv.swap (0 : Fin 8) 1 * Equiv.swap 2 3 ∉ Subgroup.zpowers (Equiv.swap (4 : Fin 8) 5) := by
  intro h
  rcases b3c_mem_zpowers_swap h with h | h <;> revert h <;> decide

private theorem b3c_zpowers_lt_A0 : Subgroup.zpowers (Equiv.swap (4 : Fin 8) 5) < B3.A0 8 :=
  lt_of_le_of_ne (Subgroup.zpowers_le.2 b3c_swap45_mem_A0)
    (fun h => b3c_dt_not_mem (h ▸ b3c_dt_mem_A0))

open CFSG.Quasithin.B3 in
theorem exists_swap_lt_of_mem_conjClass_A0 {A : Subgroup P8} (hA : A ∈ B3.conjClass (B3.A0 8)) :
    ∃ a b : Fin 8, a ≠ b ∧ Subgroup.zpowers (Equiv.swap a b) < A := by
  obtain ⟨γ, rfl⟩ := hA
  rw [b3c_cj_eq]
  exact b3c_exists_swap_lt_cjP γ (by decide) b3c_zpowers_lt_A0

private theorem b3c_ti_eq_swap {i : ℕ} (hi : i < 4) :
    ∃ a b : Fin 8, a ≠ b ∧ B3.ti 8 i = Equiv.swap a b := by
  interval_cases i
  · exact ⟨0, 1, by decide, by decide⟩
  · exact ⟨2, 3, by decide, by decide⟩
  · exact ⟨4, 5, by decide, by decide⟩
  · exact ⟨6, 7, by decide, by decide⟩

private theorem b3c_ti_mem_Dsub {i : ℕ} (hi : i < 4) : B3.ti 8 i ∈ B3.Dsub 8 := by
  apply Subgroup.subset_closure
  simp only [B3.gensAm, List.mem_map, List.mem_range, Set.mem_ofPred_eq]
  exact ⟨i, by omega, rfl⟩

private theorem b3c_sign_ti {i : ℕ} (hi : i < 4) : Equiv.Perm.sign (B3.ti 8 i) = -1 := by
  obtain ⟨a, b, hab, h⟩ := b3c_ti_eq_swap hi
  rw [h, Equiv.Perm.sign_swap hab]

private theorem b3c_relIndex_eq_two {H D : Subgroup P8} (hHD : H ≤ D)
    (hcard : Nat.card D = 2 * Nat.card H) : H.relIndex D = 2 := by
  have h1 := Subgroup.relIndex_mul_card H D
  rw [inf_of_le_left hHD] at h1
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans hcard)

private theorem b3c_relIndex_DL :
    (B3.Dsub 8 ⊓ alternatingGroup (Fin 8)).relIndex (B3.Dsub 8) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨B3.ti 8 0, b3c_ti_mem_Dsub (by decide), fun b hb => ?_⟩
  rw [xor_iff_iff_not]
  have hba : b * B3.ti 8 0 ∈ B3.Dsub 8 := (B3.Dsub 8).mul_mem hb (b3c_ti_mem_Dsub (by decide))
  simp only [Subgroup.mem_inf, hb, hba, true_and, Equiv.Perm.mem_alternatingGroup, map_mul,
    b3c_sign_ti (show 0 < 4 by decide)]
  rcases Int.units_eq_one_or (Equiv.Perm.sign b) with h | h <;> simp [h]

private theorem b3c_mul_mem_iff {H D : Subgroup P8} (hH : H.relIndex D = 2) {x y : P8}
    (hx : x ∈ D) (hy : y ∈ D) : x * y ∈ H ↔ (x ∈ H ↔ y ∈ H) := by
  have := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf D) hH (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  simpa [Subgroup.mem_subgroupOf] using this

private theorem b3c_exists_ti_mem {H : Subgroup P8} (hHD : H ≤ B3.Dsub 8)
    (hcard : Nat.card (B3.Dsub 8) = 2 * Nat.card H)
    (hne : H ≠ B3.Dsub 8 ⊓ alternatingGroup (Fin 8)) : ∃ i < 4, B3.ti 8 i ∈ H := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hH := b3c_relIndex_eq_two hHD hcard
  have hE := b3c_relIndex_DL
  ext x
  by_cases hx : x ∈ B3.Dsub 8
  · have key : ∀ y (hy : y ∈ B3.Dsub 8),
        (y ∈ H ↔ y ∈ B3.Dsub 8 ⊓ alternatingGroup (Fin 8)) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨i, hi, rfl⟩ : ∃ i < 4, B3.ti 8 i = y := by
          simp only [B3.gensAm, List.mem_map, List.mem_range, Set.mem_ofPred_eq] at hy
          obtain ⟨i, hi, h⟩ := hy
          exact ⟨i, by omega, h⟩
        refine iff_of_false (hcon i hi) ?_
        rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup, b3c_sign_ti hi]
        exact fun h => absurd h.2 (by decide)
      | one => exact iff_of_true (one_mem _) (one_mem _)
      | mul y z hy hz ihy ihz =>
        rw [b3c_mul_mem_iff hH hy hz, b3c_mul_mem_iff hE hy hz, ihy, ihz]
      | inv y hy ih => rw [inv_mem_iff, inv_mem_iff, ih]
    exact key x hx
  · exact iff_of_false (fun h => hx (hHD h)) (fun h => hx h.1)

private theorem b3c_five_le_card_Dsub : 5 ≤ Nat.card (B3.Dsub 8) := by
  classical
  have hmem : ∀ x ∈ ({1, B3.ti 8 0, B3.ti 8 1, B3.ti 8 2, B3.ti 8 3} : Finset P8),
      x ∈ B3.Dsub 8 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact b3c_ti_mem_Dsub (by decide)
    · exact b3c_ti_mem_Dsub (by decide)
    · exact b3c_ti_mem_Dsub (by decide)
    · exact b3c_ti_mem_Dsub (by decide)
  have hc : ({1, B3.ti 8 0, B3.ti 8 1, B3.ti 8 2, B3.ti 8 3} : Finset P8).card = 5 := by decide
  have h := Set.ncard_le_ncard
    (s := (↑({1, B3.ti 8 0, B3.ti 8 1, B3.ti 8 2, B3.ti 8 3} : Finset P8) : Set P8))
    (t := (B3.Dsub 8 : Set P8)) (fun x hx => hmem x hx) (Set.toFinite _)
  rw [Set.ncard_coe_finset, hc, ← Nat.card_coe_set_eq] at h
  exact h

private theorem b3c_orderOf_swap {a b : Fin 8} (hab : a ≠ b) : orderOf (Equiv.swap a b) = 2 :=
  orderOf_eq_prime (by rw [pow_two, Equiv.swap_mul_self])
    (fun h => hab (Equiv.swap_eq_one_iff.1 h))

open CFSG.Quasithin.B3 in
theorem exists_swap_lt_of_mem_Hset {A : Subgroup P8} (hA : A ∈ B3.Hset 8) :
    ∃ a b : Fin 8, a ≠ b ∧ Subgroup.zpowers (Equiv.swap a b) < A := by
  obtain ⟨γ, H, hHD, hcard, hne, rfl⟩ := hA
  obtain ⟨i, hi, hiH⟩ := b3c_exists_ti_mem hHD hcard hne
  obtain ⟨a, b, hab, hab'⟩ := b3c_ti_eq_swap hi
  rw [hab'] at hiH
  have hlt : Subgroup.zpowers (Equiv.swap a b) < H := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.2 hiH) fun heq => ?_
    have h2 : Nat.card H = 2 := by rw [← heq, Nat.card_zpowers, b3c_orderOf_swap hab]
    have h5 := b3c_five_le_card_Dsub
    omega
  rw [b3c_cj_eq]
  exact b3c_exists_swap_lt_cjP γ hab hlt

private theorem b3c_dsub_eq : B3.Dsub 8 = D8 := by
  unfold B3.Dsub B3.Am D8
  congr 1
  ext g
  simp only [B3.gensAm, List.mem_map, List.mem_range, Set.mem_ofPred_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : i < 4 := by omega
    interval_cases i
    · left; decide
    · right; left; decide
    · right; right; left; decide
    · right; right; right; decide
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨3, by decide, by decide⟩

open CFSG.Quasithin.B3 in
theorem exists_cjP_of_mem_conjClass_DL {A : Subgroup P8}
    (hA : A ∈ B3.conjClass (B3.Dsub 8 ⊓ alternatingGroup (Fin 8))) :
    ∃ γ : P8, A = cjP γ (D8 ⊓ alternatingGroup (Fin 8)) := by
  obtain ⟨γ, hγ⟩ := hA
  exact ⟨γ, by rw [hγ, b3c_cj_eq, b3c_dsub_eq]⟩

end CFSG.Quasithin.A38c6
