module

public import CFSG.Quasithin.Background.HModChk
public import CFSG.Quasithin.Background.H16TwoM22Check
public import CFSG.Quasithin.Background.H16TwoM22PfA
public import CFSG.Quasithin.Background.RonanH143Vocab

public section

namespace CFSG.ASVolI.H16

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.RonanH143

@[expose] def h165Z0 : Equiv.Perm (Fin 24) := koPerm 7

@[expose] def h165D0Arr : Array ℕ :=
  #[1, 0, 4, 5, 2, 3, 7, 6, 8, 9, 13, 12, 11, 10, 14, 15, 23, 22, 18, 19, 20, 21, 17, 16]

@[expose] def h165ZD0Arr : Array ℕ :=
  #[1, 0, 4, 5, 2, 3, 7, 6, 15, 14, 10, 11, 12, 13, 9, 8, 16, 17, 21, 20, 19, 18, 22, 23]

theorem h165D0_ok : InvPairOK 24 h165D0Arr h165D0Arr = true ∧ autArrOK h165D0Arr h165D0Arr = true ∧
    h165D0Arr[0]! = 1 ∧ h165D0Arr[1]! = 0 := by
  decide +kernel

theorem h165ZD0_ok : InvPairOK 24 h165ZD0Arr h165ZD0Arr = true ∧
    autArrOK h165ZD0Arr h165ZD0Arr = true ∧ h165ZD0Arr[0]! = 1 ∧ h165ZD0Arr[1]! = 0 := by
  decide +kernel

@[expose] def h165D0 : Equiv.Perm (Fin 24) := permOfArr 24 h165D0Arr h165D0Arr h165D0_ok.1

@[expose] def h165ZD0 : Equiv.Perm (Fin 24) := permOfArr 24 h165ZD0Arr h165ZD0Arr h165ZD0_ok.1

theorem hasArr_h165Z0 : HasArr h165Z0 (koArr 7) := hasArr_permOfArr (koArr_ok 7).1

theorem hasArr_h165D0 : HasArr h165D0 h165D0Arr := hasArr_permOfArr h165D0_ok.1

theorem hasArr_h165ZD0 : HasArr h165ZD0 h165ZD0Arr := hasArr_permOfArr h165ZD0_ok.1

theorem h165Z0_mem : h165Z0 ∈ mog22plus := mog22_le_mog22plus (koPerm_mem_mog22 7)

theorem h165D0_mem : h165D0 ∈ mog22plus :=
  ⟨mem_AutPerm_of_arr h165D0_ok.1 h165D0_ok.2.1,
    Or.inr ⟨hasArr_h165D0.apply_eq 0 h165D0_ok.2.2.1, hasArr_h165D0.apply_eq 1 h165D0_ok.2.2.2⟩⟩

theorem h165ZD0_mem : h165ZD0 ∈ mog22plus :=
  ⟨mem_AutPerm_of_arr h165ZD0_ok.1 h165ZD0_ok.2.1,
    Or.inr ⟨hasArr_h165ZD0.apply_eq 0 h165ZD0_ok.2.2.1,
      hasArr_h165ZD0.apply_eq 1 h165ZD0_ok.2.2.2⟩⟩

theorem h165Z0_sq : h165Z0 * h165Z0 = 1 := by decide +kernel

theorem h165D0_sq : h165D0 * h165D0 = 1 := by decide +kernel

theorem h165ZD0_eq : h165Z0 * h165D0 = h165ZD0 := by decide +kernel

theorem h165D0_comm : h165D0 * h165Z0 = h165Z0 * h165D0 := by decide +kernel

theorem h165Z0_ne_one : h165Z0 ≠ 1 := by decide +kernel

theorem h165D0_ne_one : h165D0 ≠ 1 := by decide +kernel

theorem h165D0_ne_Z0 : h165D0 ≠ h165Z0 := by decide +kernel

@[expose] def h165PartnerArr : Array ℕ :=
  #[1, 0, 4, 5, 2, 3, 7, 6, 15, 14, 13, 12, 11, 10, 9, 8, 23, 22, 21, 20, 19, 18, 17, 16]

@[expose] def h165Partner (p : Fin 24) : Fin 24 := ⟨h165PartnerArr[(p : ℕ)]! % 24, Nat.mod_lt _ (by norm_num)⟩

theorem h165Partner_partner : ∀ p : Fin 24, h165Partner (h165Partner p) = p := by decide +kernel

theorem h165Partner_ne : ∀ p : Fin 24, h165Partner p ≠ p := by decide +kernel

@[expose] def h165Y1Arr : Array ℕ :=
  #[0, 1, 3, 6, 5, 7, 2, 4, 8, 18, 12, 22, 17, 11, 21, 15, 16, 10, 20, 14, 9, 19, 13, 23]

@[expose] def h165Y1Inv : Array ℕ :=
  #[0, 1, 6, 2, 7, 4, 3, 5, 8, 20, 17, 13, 10, 22, 19, 15, 16, 12, 9, 21, 18, 14, 11, 23]

@[expose] def h165Y2Arr : Array ℕ :=
  #[0, 1, 3, 6, 5, 7, 2, 4, 14, 20, 10, 16, 23, 13, 19, 9, 22, 12, 18, 8, 15, 21, 11, 17]

@[expose] def h165Y2Inv : Array ℕ :=
  #[0, 1, 6, 2, 7, 4, 3, 5, 19, 15, 10, 22, 17, 13, 8, 20, 11, 23, 18, 14, 9, 21, 16, 12]

@[expose] def h165Y3Arr : Array ℕ :=
  #[0, 1, 3, 7, 5, 6, 4, 2, 8, 21, 16, 13, 10, 23, 18, 15, 12, 17, 20, 9, 14, 19, 22, 11]

@[expose] def h165Y3Inv : Array ℕ :=
  #[0, 1, 7, 2, 6, 4, 5, 3, 8, 19, 12, 23, 16, 11, 20, 15, 10, 17, 14, 21, 18, 9, 22, 13]

theorem h165Y1_ok : InvPairOK 24 h165Y1Arr h165Y1Inv = true ∧ autArrOK h165Y1Arr h165Y1Inv = true ∧
    h165Y1Arr[0]! = 0 ∧ h165Y1Arr[1]! = 1 := by
  decide +kernel

theorem h165Y2_ok : InvPairOK 24 h165Y2Arr h165Y2Inv = true ∧ autArrOK h165Y2Arr h165Y2Inv = true ∧
    h165Y2Arr[0]! = 0 ∧ h165Y2Arr[1]! = 1 := by
  decide +kernel

theorem h165Y3_ok : InvPairOK 24 h165Y3Arr h165Y3Inv = true ∧ autArrOK h165Y3Arr h165Y3Inv = true ∧
    h165Y3Arr[0]! = 0 ∧ h165Y3Arr[1]! = 1 := by
  decide +kernel

@[expose] def h165Y1 : Equiv.Perm (Fin 24) := permOfArr 24 h165Y1Arr h165Y1Inv h165Y1_ok.1

@[expose] def h165Y2 : Equiv.Perm (Fin 24) := permOfArr 24 h165Y2Arr h165Y2Inv h165Y2_ok.1

@[expose] def h165Y3 : Equiv.Perm (Fin 24) := permOfArr 24 h165Y3Arr h165Y3Inv h165Y3_ok.1

theorem h165Y1_mem : h165Y1 ∈ mog22plus :=
  mog22_le_mog22plus (mem_mog22_of_arr (mem_AutPerm_of_arr h165Y1_ok.1 h165Y1_ok.2.1)
    (hasArr_permOfArr h165Y1_ok.1) h165Y1_ok.2.2.1 h165Y1_ok.2.2.2)

theorem h165Y2_mem : h165Y2 ∈ mog22plus :=
  mog22_le_mog22plus (mem_mog22_of_arr (mem_AutPerm_of_arr h165Y2_ok.1 h165Y2_ok.2.1)
    (hasArr_permOfArr h165Y2_ok.1) h165Y2_ok.2.2.1 h165Y2_ok.2.2.2)

theorem h165Y3_mem : h165Y3 ∈ mog22plus :=
  mog22_le_mog22plus (mem_mog22_of_arr (mem_AutPerm_of_arr h165Y3_ok.1 h165Y3_ok.2.1)
    (hasArr_permOfArr h165Y3_ok.1) h165Y3_ok.2.2.1 h165Y3_ok.2.2.2)

theorem h165Y1_comm : h165Z0 * h165Y1 = h165Y1 * h165Z0 := by decide +kernel

theorem h165Y2_comm : h165Z0 * h165Y2 = h165Y2 * h165Z0 := by decide +kernel

theorem h165Y3_comm : h165Z0 * h165Y3 = h165Y3 * h165Z0 := by decide +kernel

theorem h165Y1_cube : h165Y1 ^ 3 = 1 := by decide +kernel

theorem h165Y2_cube : h165Y2 ^ 3 = 1 := by decide +kernel

theorem h165Y3_cube : h165Y3 ^ 3 = 1 := by decide +kernel

theorem hasArr_h165Y1 : HasArr h165Y1 h165Y1Arr := hasArr_permOfArr h165Y1_ok.1

theorem hasArr_h165Y2 : HasArr h165Y2 h165Y2Arr := hasArr_permOfArr h165Y2_ok.1

theorem hasArr_h165Y3 : HasArr h165Y3 h165Y3Arr := hasArr_permOfArr h165Y3_ok.1

theorem hasArr_h165Y1_inv : HasArr h165Y1⁻¹ h165Y1Inv := hasArr_permOfArr_inv h165Y1_ok.1

theorem hasArr_h165Y2_inv : HasArr h165Y2⁻¹ h165Y2Inv := hasArr_permOfArr_inv h165Y2_ok.1

theorem hasArr_h165Y3_inv : HasArr h165Y3⁻¹ h165Y3Inv := hasArr_permOfArr_inv h165Y3_ok.1

@[expose] def h165K0 : List (Equiv.Perm (Fin 24)) :=
  [h165Y1, h165Y2, h165Y3, h165Y2 * h165Y1, h165Y3⁻¹ * h165Y1, h165Y3 * h165Y1⁻¹,
    h165Y2⁻¹ * h165Y1]

@[expose] def h165K0Arr : List (Array ℕ) :=
  [h165Y1Arr, h165Y2Arr, h165Y3Arr, cArr h165Y2Arr h165Y1Arr, cArr h165Y3Inv h165Y1Arr,
    cArr h165Y3Arr h165Y1Inv, cArr h165Y2Inv h165Y1Arr]

theorem h165K0_sep : ∀ p q : Fin 24,
    (∀ a ∈ h165K0Arr, (a[(p : ℕ)]! = (p : ℕ) ↔ a[(q : ℕ)]! = (q : ℕ))) →
      q = p ∨ q = h165Partner p := by
  decide +kernel

theorem h165K0_hasArr : ∀ a ∈ h165K0Arr, ∃ k ∈ h165K0, HasArr k a := by
  intro a ha
  simp only [h165K0Arr, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [h165K0], hasArr_h165Y1⟩
  · exact ⟨_, by simp [h165K0], hasArr_h165Y2⟩
  · exact ⟨_, by simp [h165K0], hasArr_h165Y3⟩
  · exact ⟨_, by simp [h165K0], hasArr_mul hasArr_h165Y2 hasArr_h165Y1⟩
  · exact ⟨_, by simp [h165K0], hasArr_mul hasArr_h165Y3_inv hasArr_h165Y1⟩
  · exact ⟨_, by simp [h165K0], hasArr_mul hasArr_h165Y3 hasArr_h165Y1_inv⟩
  · exact ⟨_, by simp [h165K0], hasArr_mul hasArr_h165Y2_inv hasArr_h165Y1⟩

theorem h165_K0_comm_pair {g : Equiv.Perm (Fin 24)} (hg : ∀ k ∈ h165K0, g * k = k * g)
    (p : Fin 24) : g p = p ∨ g p = h165Partner p := by
  refine h165K0_sep p (g p) fun a ha => ?_
  obtain ⟨k, hk, hka⟩ := h165K0_hasArr a ha
  have h1 : ((k p : Fin 24) : ℕ) = a[(p : ℕ)]! := hka p
  have h2 : ((k (g p) : Fin 24) : ℕ) = a[((g p : Fin 24) : ℕ)]! := hka (g p)
  rw [← h1, ← h2]
  have hcomm : k (g p) = g (k p) := by
    have := congrArg (fun σ => σ p) (hg k hk)
    simpa using this.symm
  simp only [Fin.val_inj]
  rw [hcomm, g.injective.eq_iff]

@[expose] def h165OctMasks : List ℕ := [0xFF, 0x248117, 0x3C00C3, 0xFF00, 0xA5A500, 0xC3C300]

theorem h165Oct_syndM : ∀ m ∈ h165OctMasks, syndM m = 0 := by decide +kernel

theorem h165Oct_pair : ∀ m ∈ h165OctMasks, m.testBit 0 = m.testBit 1 := by decide +kernel

theorem h165Oct_Z0 : ∀ m ∈ h165OctMasks, ∀ p : Fin 24, m.testBit (h165Z0 p) = m.testBit p := by
  decide +kernel

theorem h165Oct_sep : ∀ p q : Fin 24, (∀ m ∈ h165OctMasks, m.testBit p = m.testBit q) →
    q = p ∨ q = h165Partner p := by
  decide +kernel

end CFSG.ASVolI.H16
