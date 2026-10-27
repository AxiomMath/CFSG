module

public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB

public section

namespace CFSG.Quasithin.H13.S6Syl

@[expose] def gen : Fin 3 → Equiv.Perm (Fin 6) :=
  ![Equiv.swap 0 1, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 4 5]

@[expose] def evalS (w : List (Fin 3)) : Equiv.Perm (Fin 6) := w.foldl (fun P k => P * gen k) 1

@[expose] def wordsS : List (List (Fin 3)) :=
  [[], [2], [1, 0, 1], [1, 0, 1, 2], [0], [0, 2], [0, 1, 0, 1], [0, 1, 0, 1, 2], [1], [1, 2],
    [0, 1], [0, 1, 2], [1, 0], [1, 0, 2], [0, 1, 0], [0, 1, 0, 2]]

@[expose] def elemsS : List (Equiv.Perm (Fin 6)) := wordsS.map evalS

theorem closed_mul : ∀ x ∈ elemsS, ∀ y ∈ elemsS, x * y ∈ elemsS := by decide +kernel

theorem closed_inv : ∀ x ∈ elemsS, x⁻¹ ∈ elemsS := by decide +kernel

theorem one_mem : (1 : Equiv.Perm (Fin 6)) ∈ elemsS := by decide +kernel

theorem gen_mem : ∀ k : Fin 3, gen k ∈ elemsS := by decide +kernel

theorem nodup : elemsS.Nodup := by decide +kernel

@[expose] def sylS : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {x | x ∈ elemsS}
  mul_mem' := fun {_ _} ha hb => closed_mul _ ha _ hb
  one_mem' := one_mem
  inv_mem' := fun {_} ha => closed_inv _ ha

theorem evalS_mem (w : List (Fin 3)) : evalS w ∈ sylowS6 := by
  unfold evalS
  suffices h : ∀ P : Equiv.Perm (Fin 6), P ∈ sylowS6 → w.foldl (fun P k => P * gen k) P ∈ sylowS6
    from h 1 (Subgroup.one_mem _)
  induction w with
  | nil => intro P h; exact h
  | cons k w ih =>
    intro P h
    simp only [List.foldl_cons]
    refine ih _ (Subgroup.mul_mem _ h (Subgroup.subset_closure ?_))
    fin_cases k <;> simp [gen]

theorem sylowS6_eq : sylowS6 = sylS := by
  refine le_antisymm ?_ ?_
  · rw [sylowS6, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact gen_mem 0
    · exact gen_mem 1
    · exact gen_mem 2
  · intro x hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
    exact evalS_mem w

theorem card_sylowS6 : Nat.card sylowS6 = 16 := by
  rw [sylowS6_eq]
  have h : Nat.card sylS = elemsS.toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [sylS])
  rw [h, List.toFinset_card_of_nodup nodup]
  rfl

@[expose] def elemsA : List (Equiv.Perm (Fin 6)) :=
  [1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 4 5,
    Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5]

theorem center_check : ∀ x ∈ elemsS, (∀ y ∈ elemsS, x * y = y * x) ↔ x ∈ elemsA := by
  decide +kernel

theorem aBar2_eq : ∀ x : Equiv.Perm (Fin 6), x ∈ aBar2 ↔ x ∈ elemsA := by
  have hcl : ∀ x ∈ elemsA, ∀ y ∈ elemsA, x * y ∈ elemsA := by decide +kernel
  have hinv : ∀ x ∈ elemsA, x⁻¹ ∈ elemsA := by decide +kernel
  have h1 : (1 : Equiv.Perm (Fin 6)) ∈ elemsA := by decide +kernel
  let A : Subgroup (Equiv.Perm (Fin 6)) :=
    { carrier := {x | x ∈ elemsA}
      mul_mem' := fun {_ _} ha hb => hcl _ ha _ hb
      one_mem' := h1
      inv_mem' := fun {_} ha => hinv _ ha }
  have hle : aBar2 ≤ A := by
    rw [aBar2, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · show _ ∈ elemsA; decide +kernel
    · show _ ∈ elemsA; decide +kernel
  intro x
  refine ⟨fun hx => hle hx, fun hx => ?_⟩
  have g1 : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 ∈ aBar2 :=
    Subgroup.subset_closure (by simp)
  have g2 : Equiv.swap (4 : Fin 6) 5 ∈ aBar2 := Subgroup.subset_closure (by simp)
  simp only [elemsA, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact g1
  · exact g2
  · exact Subgroup.mul_mem _ g1 g2

theorem mem_center_iff (x : Equiv.Perm (Fin 6)) :
    (x ∈ sylowS6 ∧ ∀ y ∈ sylowS6, x * y = y * x) ↔ x ∈ aBar2 := by
  rw [aBar2_eq, sylowS6_eq]
  constructor
  · rintro ⟨hx, h⟩
    exact (center_check x hx).mp fun y hy => h y hy
  · intro hx
    have hxS : x ∈ elemsS := by
      simp only [elemsA, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel
    exact ⟨hxS, fun y hy => (center_check x hxS).mpr hx y hy⟩

theorem aBar2_le_sylowS6 : aBar2 ≤ sylowS6 := fun x hx => ((mem_center_iff x).mpr hx).1

theorem card_perm_six : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem exists_conj_eq_sylowS6 {P : Subgroup (Equiv.Perm (Fin 6))} (hP : Nat.card P = 16) :
    ∃ g : Equiv.Perm (Fin 6), P = sylowS6.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card (Equiv.Perm (Fin 6))).factorization 2 = 4 := by
    have hprod : (720 : ℕ) = 2 ^ 4 * 45 := by norm_num
    rw [card_perm_six, hprod, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 45)]
  let S₁ : Sylow 2 (Equiv.Perm (Fin 6)) :=
    Sylow.ofCard P (by rw [hP, hfac]; norm_num)
  let S₂ : Sylow 2 (Equiv.Perm (Fin 6)) :=
    Sylow.ofCard sylowS6 (by rw [card_sylowS6, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 6)) S₂ S₁
  refine ⟨g, ?_⟩
  have h1 := congrArg Sylow.toSubgroup hg
  calc P = (S₁ : Subgroup (Equiv.Perm (Fin 6))) := rfl
    _ = ((g • S₂ : Sylow 2 (Equiv.Perm (Fin 6))) : Subgroup (Equiv.Perm (Fin 6))) := h1.symm
    _ = sylowS6.map (MulAut.conj g).toMonoidHom := rfl

end CFSG.Quasithin.H13.S6Syl
