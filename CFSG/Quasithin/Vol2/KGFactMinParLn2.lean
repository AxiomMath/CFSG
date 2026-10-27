module

public import CFSG.Quasithin.Vol2.KGFactMinParL42
public import CFSG.Quasithin.Vol2.KGFactMinParL52
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310KG
public import CFSG.LargeExtraspecial.OutSixBasic
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.Quasithin.H13.KGMinPar

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type} [Group X]

theorem ln2_index_dvd [Finite X] {L : Subgroup X} [L.Normal]
    (hC : Subgroup.centralizer (L : Set X) = ⊥) {n : ℕ} (hn : 3 ≤ n)
    (h : StatedClassicalModel ↥L .PSL n 2 1) : L.index ∣ 2 := by
  have h1 := CFSG.LargeExtraspecial.S14.index_dvd_card_outer L (by rw [hC]; exact bot_le)
  obtain ⟨h2, -⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (T := ↥L) (Or.inl rfl) hn Nat.prime_two le_rfl h
  have h3 : CFSG.RankThree.OuterOrder.determinantParameter .PSL n (2 ^ 1) = 1 := by
    simp [CFSG.RankThree.OuterOrder.determinantParameter]
  rw [h3] at h2
  exact h1.trans (by simpa using h2)

theorem kg8310MinParLn2_holds :
    KG8310MinParLn2 := by
  intro X _ _ L S P hLn hL hC hS hP
  have hT : IsSylowTwoOf (S ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hS le_top (by rw [Subgroup.normalizer_eq_top])
  rcases hL with h4 | h5
  · obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
      ↥L).mp (Or.inl ⟨by decide, h4⟩)
    exact not_five_dvd (ln2_index_dvd hC (by norm_num) h4) hS (l42_key hT e) hP.1
  · have hidx := ln2_index_dvd hC (by norm_num) h5
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h5
    have e' : ↥L ≃* CFSG.Literature.GL52.G :=
      (e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 5 K
        (by simpa using hK))).trans
        (MulEquiv.ofBijective _ CFSG.Literature.GL52.bijective_toGL)
    exact not_five_dvd hidx hS (l52_key hT e') hP.1

end CFSG.Quasithin.H13.KGMinPar
