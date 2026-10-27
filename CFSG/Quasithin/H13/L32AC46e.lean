module

public import CFSG.Quasithin.EmptyFaithful.S1421Elim
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem card_eq_six_of_perm3 {X : Type} [Group X] (h : Nonempty (X ≃* Equiv.Perm (Fin 3))) :
    Nat.card X = 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_dihedral_five_eq_ten : Nat.card (DihedralGroup 5) = 10 := by
  rw [Nat.card_eq_fintype_card, DihedralGroup.card]

theorem five_hundred_four_le_card_L2 (f : ℕ) (hf : 3 ≤ f) : 504 ≤ 2 ^ f * (4 ^ f - 1) := by
  have h8 : 8 ≤ 2 ^ f :=
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h64 : 64 ≤ 4 ^ f :=
    calc (64 : ℕ) = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h63 : 63 ≤ 4 ^ f - 1 := by omega
  calc (504 : ℕ) = 8 * 63 := by norm_num
    _ ≤ 2 ^ f * (4 ^ f - 1) := Nat.mul_le_mul h8 h63

theorem eq_one_of_isL2Quot_card_six {f : ℕ} (hf : 1 ≤ f) {X : Type} [Group X]
    (h : IsL2Quot f X) (hc : Nat.card X = 6) : f = 1 := by
  have key := IsL2Quot.card hf h
  rw [hc] at key
  by_contra hne
  rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | h3
  · norm_num at key
  · have h504 := five_hundred_four_le_card_L2 f h3
    rw [← key] at h504
    norm_num at h504

theorem false_of_isL2Quot_one_card_sixty {X : Type} [Group X] (hc : Nat.card X = 60)
    (h : IsL2Quot 1 X) : False := by
  have h1 := IsL2Quot.card le_rfl h
  rw [hc] at h1
  norm_num at h1

theorem false_of_F112List_unswapped {K I S : Subgroup G}
    (hKns : ¬ Group.IsSolvable ↥K) (hKc : Nat.card (oTwoQuot ↥K) = 60)
    (hS3 : Nonempty (oTwoQuot ↥I ≃* Equiv.Perm (Fin 3)))
    (hQ8 : ¬ IsQ8D8 ↥(pCoreOf 2 (K ⊔ bigB K I S)))
    (hl : F112List K I S) : False := by
  have hIc : Nat.card (oTwoQuot ↥I) = 6 := card_eq_six_of_perm3 hS3
  have hblk : ¬ IsBlock2 I I := S1421Elim.not_isBlock2_of_oTwoQuot_perm3 hS3
  unfold F112List at hl
  dsimp only at hl
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  ·
    obtain ⟨f, hf, -, h⟩ := h1
    rcases h with ⟨-, -, -, hb, -⟩ | ⟨-, ⟨e⟩, -⟩
    · exact hblk hb
    · exact hKns (S1421Elim.isSolvable_of_le_of_isSolvable le_sup_left
        (CFSG.Quasithin.isSolvable_of_equiv_perm_four e))
  ·
    obtain ⟨f, hf, -, h⟩ := h2
    rcases h with ⟨-, -, -, hb, -⟩ | ⟨-, ⟨e⟩, -⟩
    · exact hblk hb
    · exact hKns (S1421Elim.isSolvable_of_le_of_isSolvable le_sup_left
        (CFSG.Quasithin.isSolvable_of_equiv_z2_perm_four e))
  ·
    obtain ⟨f, hf, -, hq1, hq2, -, -⟩ := h3
    have hf1 := eq_one_of_isL2Quot_card_six hf hq2 hIc
    subst hf1
    exact false_of_isL2Quot_one_card_sixty hKc hq1
  ·
    obtain ⟨f, hf, -, hq1, -, -, -⟩ := h4
    have hc := IsL2Quot.card (show 1 ≤ 3 * f by omega) hq1
    rw [hKc] at hc
    have h504 := five_hundred_four_le_card_L2 (3 * f) (by omega)
    rw [← hc] at h504
    norm_num at h504
  ·
    obtain ⟨a, -, hsz, -, hq2, -⟩ := h5
    have ha := eq_one_of_isL2Quot_card_six (show 1 ≤ 2 * a + 1 by omega) hq2 hIc
    obtain rfl : a = 0 := by omega
    rcases hsz with ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · have hc := (Nat.card_congr e.toEquiv).trans CFSG.Quasithin.card_sz_zero
      rw [hKc] at hc
      norm_num at hc
    · have hc := (Nat.card_congr e.toEquiv).trans card_dihedral_five_eq_ten
      rw [hKc] at hc
      norm_num at hc
  ·
    obtain ⟨f, -, -, -, -, hb, -, -, -⟩ := h6
    exact hblk hb
  ·
    obtain ⟨-, -, -, hq, -⟩ := h7
    have hc := IsL2Quot.card (show 1 ≤ 4 by norm_num) hq
    rw [hIc] at hc
    norm_num at hc
  ·
    obtain ⟨-, hq1, -, -, -⟩ := h8
    exact false_of_isL2Quot_one_card_sixty hKc hq1
  ·
    obtain ⟨-, hq, -, -, -⟩ := h9
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hc := (Nat.card_congr e.toEquiv).trans card_dihedral_five_eq_ten
      rw [hKc] at hc
      norm_num at hc
    · have hc := (Nat.card_congr e.toEquiv).trans CFSG.Quasithin.card_sz_zero
      rw [hKc] at hc
      norm_num at hc
  ·
    obtain ⟨-, -, hQ, -, -⟩ := h10
    exact hQ8 hQ
  ·
    obtain ⟨-, -, hQ, -, -⟩ := h11
    exact hQ8 hQ
  ·
    obtain ⟨-, hq1, -, -, -⟩ := h12
    exact false_of_isL2Quot_one_card_sixty hKc hq1
  ·
    obtain ⟨-, hq1, -, -, -⟩ := h13
    exact false_of_isL2Quot_one_card_sixty hKc hq1

theorem false_of_F112List_swapped {I K S : Subgroup G}
    (hKns : ¬ Group.IsSolvable ↥K) (hKc : Nat.card (oTwoQuot ↥K) = 60)
    (hS3 : Nonempty (oTwoQuot ↥I ≃* Equiv.Perm (Fin 3)))
    (hZ : ¬ IsSpecialPow 2 (2 ^ 1) 2 ↥(pCoreOf 2 (I ⊔ bigB I K S)))
    (hl : F112List I K S) : False := by
  have hIc : Nat.card (oTwoQuot ↥I) = 6 := card_eq_six_of_perm3 hS3
  have hblk : ¬ IsBlock2 I I := S1421Elim.not_isBlock2_of_oTwoQuot_perm3 hS3
  unfold F112List at hl
  dsimp only at hl
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  ·
    obtain ⟨f, hf, -, h⟩ := h1
    rcases h with ⟨-, hb, -, -, -⟩ | ⟨-, -, ⟨e⟩⟩
    · exact hblk hb
    · exact hKns (S1421Elim.isSolvable_of_le_of_isSolvable le_sup_left
        (CFSG.Quasithin.isSolvable_of_equiv_perm_four e))
  ·
    obtain ⟨f, hf, -, h⟩ := h2
    rcases h with ⟨-, hb, -, -, -⟩ | ⟨-, -, ⟨e⟩⟩
    · exact hblk hb
    · exact hKns (S1421Elim.isSolvable_of_le_of_isSolvable le_sup_left
        (CFSG.Quasithin.isSolvable_of_equiv_z2_perm_four e))
  ·
    obtain ⟨f, hf, -, hq1, hq2, -, -⟩ := h3
    have hf1 := eq_one_of_isL2Quot_card_six hf hq1 hIc
    subst hf1
    exact false_of_isL2Quot_one_card_sixty hKc hq2
  ·
    obtain ⟨f, hf, -, hq1, -, -, -⟩ := h4
    have hc := IsL2Quot.card (show 1 ≤ 3 * f by omega) hq1
    rw [hIc] at hc
    have h504 := five_hundred_four_le_card_L2 (3 * f) (by omega)
    rw [← hc] at h504
    norm_num at h504
  ·
    obtain ⟨a, -, -, -, hq2, -⟩ := h5
    have hc := IsL2Quot.card (show 1 ≤ 2 * a + 1 by omega) hq2
    rw [hKc] at hc
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · norm_num at hc
    · have h504 := five_hundred_four_le_card_L2 (2 * a + 1) (by omega)
      rw [← hc] at h504
      norm_num at h504
  ·
    obtain ⟨f, hf, -, hq1, hsp, -, -, -, -⟩ := h6
    have hf1 := eq_one_of_isL2Quot_card_six hf hq1 hIc
    subst hf1
    exact hZ hsp
  ·
    obtain ⟨-, -, -, hq, -⟩ := h7
    have hc := IsL2Quot.card (show 1 ≤ 4 by norm_num) hq
    rw [hKc] at hc
    norm_num at hc
  ·
    obtain ⟨-, -, hq2, -, -⟩ := h8
    exact false_of_isL2Quot_one_card_sixty hKc hq2
  ·
    obtain ⟨-, -, -, hq2, -⟩ := h9
    exact false_of_isL2Quot_one_card_sixty hKc hq2
  ·
    obtain ⟨-, hq1, -, -, -⟩ := h10
    have hc := IsL2Quot.card (show 1 ≤ 2 by norm_num) hq1
    rw [hIc] at hc
    norm_num at hc
  ·
    obtain ⟨-, -, -, hq2, -⟩ := h11
    have hc := card_eq_six_of_perm3 hq2
    rw [hKc] at hc
    norm_num at hc
  ·
    obtain ⟨-, -, -, hq2, -⟩ := h12
    exact false_of_isL2Quot_one_card_sixty hKc hq2
  ·
    obtain ⟨-, -, -, hq2, -⟩ := h13
    exact false_of_isL2Quot_one_card_sixty hKc hq2

end CFSG.Quasithin.H13.L32A.C
