module

public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Quasithin.EmptyFaithful.S1421Elim

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S1421Elim

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_perm_three (hF : ListedGroupFacts) : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  have := hF.perm4_solvable (Equiv.Perm (Fin 4)) ⟨MulEquiv.refl _⟩
  exact Group.isSolvable_of_isSolvable_injective
    (f := Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 3 ↪ Fin 4))
    (Equiv.Perm.viaEmbeddingHom_injective _)

theorem isSolvable_of_perm_three (hF : ListedGroupFacts) {X : Type*} [Group X]
    (h : Nonempty (X ≃* Equiv.Perm (Fin 3))) : Group.IsSolvable X := by
  obtain ⟨e⟩ := h
  have := isSolvable_perm_three hF
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem f112ListA_of (hF : ListedGroupFacts) {L1 L2 S : Subgroup G}
    (hns1 : ¬ Group.IsSolvable ↥L1) (hns2 : ¬ Group.IsSolvable ↥L2)
    (hl : F112List L1 L2 S) : F112ListA L1 L2 S := by
  have hnq1 : ¬ Group.IsSolvable (oTwoQuot ↥L1) := fun h =>
    hns1 (isSolvable_of_isSolvable_oTwoQuot h)
  have hnq2 : ¬ Group.IsSolvable (oTwoQuot ↥L2) := fun h =>
    hns2 (isSolvable_of_isSolvable_oTwoQuot h)
  have hnS1 : ¬ Group.IsSolvable ↥(L1 ⊔ S) := fun h =>
    hns1 (isSolvable_of_le_of_isSolvable le_sup_left h)
  unfold F112List at hl
  unfold F112ListA
  dsimp only at hl ⊢
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · obtain ⟨f, -, hA, h⟩ := h1
    rcases h with ⟨h2f, hb1, ht1, hb2, ht2⟩ | ⟨-, ⟨e⟩, -⟩
    · exact Or.inl ⟨f, h2f, hA, hb1, ht1, hb2, ht2⟩
    · exact absurd (hF.perm4_solvable _ ⟨e⟩) hnS1
  · obtain ⟨f, -, hA, h⟩ := h2
    rcases h with ⟨h2f, hb1, ht1, hb2, ht2⟩ | ⟨-, ⟨e⟩, -⟩
    · exact Or.inr (Or.inl ⟨f, h2f, hA, hb1, ht1, hb2, ht2⟩)
    · exact absurd (hF.z2perm4_solvable _ ⟨e⟩) hnS1
  · obtain ⟨f, hf, hA, hq1, hq2, hsp, hc⟩ := h3
    have h2f : 2 ≤ f := by
      by_contra hlt
      have hf1 : f = 1 := by omega
      subst hf1
      exact hnq1 (hF.l2_one_solvable _ hq1)
    exact Or.inr (Or.inr (Or.inl ⟨f, h2f, hA, hq1, hq2, hsp, hc⟩))
  · obtain ⟨f, hf, hA, hq1, hsp, hq2, hc⟩ := h4
    have h2f : 2 ≤ f := by
      by_contra hlt
      have hf1 : f = 1 := by omega
      subst hf1
      exact hnq2 (hF.l2_one_solvable _ hq2)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h2f, hA, hq1, hsp, hq2, hc⟩)))
  · obtain ⟨a, hA, hsz, hc1, hq2, hc2⟩ := h5
    rcases hsz with ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · have ha : 1 ≤ a := by
        by_contra hlt
        have ha0 : a = 0 := by omega
        subst ha0
        exact hnq1 (hF.sz0_solvable _ ⟨e⟩)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, hA, ⟨e⟩, hc1, hq2, hc2⟩))))
    · exact absurd (hF.dihedral5_solvable _ ⟨e⟩) hnq1
  · obtain ⟨f, hf, hA, hq1, hsp, hb2, hq2, hO, -⟩ := h6
    have h2f : 2 ≤ f := by
      by_contra hlt
      have hf1 : f = 1 := by omega
      subst hf1
      exact hnq1 (hF.l2_one_solvable _ hq1)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f, h2f, hA, hq1, hsp, hb2, hq2, hO⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7)))))
  · obtain ⟨-, hq1, -⟩ := h8
    exact absurd (hF.l2_one_solvable _ hq1) hnq1
  · obtain ⟨-, -, -, hq2, -⟩ := h9
    exact absurd (hF.l2_one_solvable _ hq2) hnq2
  · obtain ⟨-, -, -, hq2, -⟩ := h10
    exact absurd (hF.l2_one_solvable _ hq2) hnq2
  · obtain ⟨-, -, -, he, -⟩ := h11
    exact absurd (isSolvable_of_perm_three hF he) hnq2
  · obtain ⟨-, hq1, -⟩ := h12
    exact absurd (hF.l2_one_solvable _ hq1) hnq1
  · obtain ⟨-, hq1, -⟩ := h13
    exact absurd (hF.l2_one_solvable _ hq1) hnq1

theorem f112ListB_unswapped (hF : ListedGroupFacts) {L1 L2 S : Subgroup G}
    (hns1 : ¬ Group.IsSolvable ↥L1) (hS3 : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)))
    (hl : F112List L1 L2 S) : F112ListB L1 L2 S := by
  have hnq1 : ¬ Group.IsSolvable (oTwoQuot ↥L1) := fun h =>
    hns1 (isSolvable_of_isSolvable_oTwoQuot h)
  have hnS1 : ¬ Group.IsSolvable ↥(L1 ⊔ S) := fun h =>
    hns1 (isSolvable_of_le_of_isSolvable le_sup_left h)
  have hblk : ¬ IsBlock2 L2 L2 := not_isBlock2_of_oTwoQuot_perm3 hS3
  unfold F112List at hl
  unfold F112ListB
  dsimp only at hl ⊢
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exfalso
    obtain ⟨f, -, -, h⟩ := h1
    rcases h with ⟨-, -, -, hb, -⟩ | ⟨-, ⟨e⟩, -⟩
    · exact hblk hb
    · exact hnS1 (hF.perm4_solvable _ ⟨e⟩)
  · exfalso
    obtain ⟨f, -, -, h⟩ := h2
    rcases h with ⟨-, -, -, hb, -⟩ | ⟨-, ⟨e⟩, -⟩
    · exact hblk hb
    · exact hnS1 (hF.z2perm4_solvable _ ⟨e⟩)
  · exfalso
    obtain ⟨f, hf, -, hq1, hq2, -⟩ := h3
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq2
    subst this
    exact hnq1 (hF.l2_one_solvable _ hq1)
  · obtain ⟨f, hf, hA, hq1, hsp, hq2, hcard⟩ := h4
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq2
    subst this
    exact Or.inl ⟨hA, hq1, hsp, hq2, hcard⟩
  · exfalso
    obtain ⟨a, -, hsz, -, hq2, -⟩ := h5
    have h1a := eq_one_of_isL2Quot_of_perm3 hF hS3 (by omega) hq2
    have ha : a = 0 := by omega
    subst ha
    rcases hsz with ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exact hnq1 (hF.sz0_solvable _ ⟨e⟩)
    · exact hnq1 (hF.dihedral5_solvable _ ⟨e⟩)
  · exfalso
    obtain ⟨-, -, -, -, -, hb, -⟩ := h6
    exact hblk hb
  · exfalso
    obtain ⟨-, -, -, hq2, -⟩ := h7
    exact false_of_isL2Quot_of_perm3 hF hS3 (by norm_num) hq2
  · exfalso
    obtain ⟨-, hq1, -⟩ := h8
    exact hnq1 (hF.l2_one_solvable _ hq1)
  · exfalso
    obtain ⟨-, hq, -⟩ := h9
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact hnq1 (hF.dihedral5_solvable _ ⟨e⟩)
    · exact hnq1 (hF.sz0_solvable _ ⟨e⟩)
  · exact Or.inr (Or.inr (Or.inl h10))
  · exact Or.inr (Or.inr (Or.inr h11))
  · exfalso
    obtain ⟨-, hq1, -⟩ := h12
    exact hnq1 (hF.l2_one_solvable _ hq1)
  · exfalso
    obtain ⟨-, hq1, -⟩ := h13
    exact hnq1 (hF.l2_one_solvable _ hq1)

theorem f112ListB_swapped (hF : ListedGroupFacts) {L1 L2 S : Subgroup G}
    (hns1 : ¬ Group.IsSolvable ↥L1) (hS3 : Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)))
    (hl : F112List L2 L1 S) : F112ListB L2 L1 S := by
  have hnq1 : ¬ Group.IsSolvable (oTwoQuot ↥L1) := fun h =>
    hns1 (isSolvable_of_isSolvable_oTwoQuot h)
  have hnS1 : ¬ Group.IsSolvable ↥(L1 ⊔ S) := fun h =>
    hns1 (isSolvable_of_le_of_isSolvable le_sup_left h)
  have hblk : ¬ IsBlock2 L2 L2 := not_isBlock2_of_oTwoQuot_perm3 hS3
  unfold F112List at hl
  unfold F112ListB
  dsimp only at hl ⊢
  rcases hl with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exfalso
    obtain ⟨f, -, -, h⟩ := h1
    rcases h with ⟨-, hb, -⟩ | ⟨-, -, ⟨e⟩⟩
    · exact hblk hb
    · exact hnS1 (hF.perm4_solvable _ ⟨e⟩)
  · exfalso
    obtain ⟨f, -, -, h⟩ := h2
    rcases h with ⟨-, hb, -⟩ | ⟨-, -, ⟨e⟩⟩
    · exact hblk hb
    · exact hnS1 (hF.z2perm4_solvable _ ⟨e⟩)
  · exfalso
    obtain ⟨f, hf, -, hq1, hq2, -⟩ := h3
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq1
    subst this
    exact hnq1 (hF.l2_one_solvable _ hq2)
  · exfalso
    obtain ⟨f, hf, -, hq1, -⟩ := h4
    exact false_of_isL2Quot_of_perm3 hF hS3 (by omega) hq1
  · exfalso
    obtain ⟨a, -, hsz, -⟩ := h5
    rcases hsz with ⟨⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · exact hF.sz_ne_perm3 a _ ⟨e⟩ hS3
    · exact hF.dihedral5_ne_perm3 _ ⟨e⟩ hS3
  · obtain ⟨f, hf, hA, hq1, hsp, hb, hq2, hO, hA5⟩ := h6
    have := eq_one_of_isL2Quot_of_perm3 hF hS3 hf hq1
    subst this
    exact Or.inr (Or.inl ⟨hA, hq1, hsp, hb, hq2, hO, hA5 rfl⟩)
  · exfalso
    obtain ⟨-, ⟨F, _, _, hF16, ⟨e⟩⟩, -⟩ := h7
    exact hF.su3_ne_perm3 _ F hF16 ⟨e⟩ hS3
  · exfalso
    obtain ⟨-, -, hq2, -⟩ := h8
    exact hnq1 (hF.l2_one_solvable _ hq2)
  · exfalso
    obtain ⟨-, hq, -⟩ := h9
    rcases hq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact hF.dihedral5_ne_perm3 _ ⟨e⟩ hS3
    · exact hF.sz_ne_perm3 0 _ ⟨e⟩ hS3
  · exfalso
    obtain ⟨-, hq1, -⟩ := h10
    exact false_of_isL2Quot_of_perm3 hF hS3 (by norm_num) hq1
  · exfalso
    obtain ⟨-, -, -, he, -⟩ := h11
    exact hnq1 (isSolvable_of_perm_three hF he)
  · exfalso
    obtain ⟨-, -, -, hq2, -⟩ := h12
    exact hnq1 (hF.l2_one_solvable _ hq2)
  · exfalso
    obtain ⟨-, -, -, hq2, -⟩ := h13
    exact hnq1 (hF.l2_one_solvable _ hq2)

end CFSG.Quasithin.H13
