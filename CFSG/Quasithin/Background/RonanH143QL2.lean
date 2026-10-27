module

public import CFSG.Quasithin.Background.RonanH143Data2
public import CFSG.Quasithin.Background.RonanH143QL
public import CFSG.Quasithin.Background.RonanH143Orb2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin

theorem card_MY_Q_L2_le :
    Nat.card ↥(MY mog22plus Qstd) ≤ 3840 := by
  have h1 := Subgroup.card_le_of_le (MY_Q_le_stab_B mog22plus)
  rw [card_inf_stabilizer_eq (Γ := mog22plus) Bstd] at h1
  obtain ⟨h1', h2, h3, h4⟩ := bfsB_checks
  have := card_stab_plus_mul_le h1' h2 h3
  rw [h4] at this
  have h5 : Nat.card (MulAction.stabilizer ↥mog22plus Bstd) ≤ 3840 := by
    show Nat.card (MulAction.stabilizer ↥mog22plus (maskSet 195)) ≤ 3840
    omega
  exact h1.trans h5

theorem NQ2_le_MY_Q : NQ2 ≤ MY mog22plus Qstd := fun g hg => by
  obtain ⟨u, rfl⟩ := hg
  refine mem_MY_Q_of_perm ?_ 1 fun i => by simpa using nq2_smul_Zq u i
  by_cases hu : (u : ℕ) < 16
  · simp only [nq2Perm, hu, ↓reduceIte]
    exact mog22_le_mog22plus (nqPerm_mem_mog22 _)
  · simp only [nq2Perm, hu, ↓reduceIte]
    exact mog22plus.mul_mem (mog22_le_mog22plus (nqPerm_mem_mog22 _)) ePerm_mem_mog22plus

theorem nq2_fix_Zq : ∀ g ∈ NQ2, ∀ i, g • Zq i = Zq i := by
  rintro _ ⟨u, rfl⟩ i
  exact nq2_smul_Zq u i

theorem g1Perm_mem_mog22plus : g1Perm ∈ mog22plus := mog22_le_mog22plus g1Perm_mem_mog22

theorem g2Perm_mem_mog22plus : g2Perm ∈ mog22plus := mog22_le_mog22plus g2Perm_mem_mog22

theorem ker_piQ_L2 :
    (piQ mog22plus).ker = NQ2.subgroupOf (MY mog22plus Qstd) :=
  ker_piQ_of_card g1Perm_mem_mog22plus g2Perm_mem_mog22plus NQ2 NQ2_le_MY_Q nq2_fix_Zq
    (by rw [card_NQ2]; exact card_MY_Q_L2_le)

theorem piQ_range_top_L2 : (piQ mog22plus).range = ⊤ :=
  piQ_range_top g1Perm_mem_mog22plus g2Perm_mem_mog22plus

theorem KY_Q_L2 :
    KY mog22plus Qstd = NQ2 :=
  pCoreOf_eq_of_ker (n := 5) (by norm_num) (piQ mog22plus) (Or.inl piQ_range_top_L2) ker_piQ_L2
    NQ2_le_MY_Q isPGroup_NQ2

theorem ePerm_notMem_mog22 : ePerm ∉ mog22 := by
  intro h
  have h0 : ePerm 0 = 0 := (mem_stab_iff 0 _).1 h.1.2
  have : ePerm 0 = 1 := hasArr_ePerm.apply_eq 0 e_ok.2.2.1
  rw [h0] at this
  exact absurd this (by decide)

theorem MY_plus_inf_mog22 {α : Type*} [MulAction P24 α] (Y : α) :
    MY mog22plus Y ⊓ mog22 = MY mog22 Y := by
  ext g
  simp only [MY, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h3, h2⟩
    exact ⟨⟨mog22_le_mog22plus h3, h2⟩, h3⟩

theorem NQ2_inf_mog22 : NQ2 ⊓ mog22 = NQ := by
  apply le_antisymm
  · rintro g ⟨⟨u, rfl⟩, hg⟩
    by_cases hu : (u : ℕ) < 16
    · refine ⟨⟨u % 16, by omega⟩, ?_⟩
      simp only [nq2Perm, hu, ↓reduceIte]
    · exfalso
      simp only [nq2Perm, hu, ↓reduceIte] at hg
      have h1 : ePerm ∈ mog22 := by
        have := mog22.mul_mem (mog22.inv_mem (nqPerm_mem_mog22 ⟨u % 16, by omega⟩)) hg
        simpa using this
      exact ePerm_notMem_mog22 h1
  · exact le_inf NQ_le_NQ2 NQ_le_mog22

theorem P2_inf_mog22 : P2 ⊓ mog22 = PO := by
  apply le_antisymm
  · rintro g ⟨⟨y, hy, rfl | rfl⟩, hg⟩
    · exact hy
    · exfalso
      have h1 : ePerm ∈ mog22 := by
        have := mog22.mul_mem (mog22.inv_mem (PO_le_mog22 hy)) hg
        simpa using this
      exact ePerm_notMem_mog22 h1
  · exact le_inf PO_le_P2 PO_le_mog22

end CFSG.Quasithin.RonanH143
