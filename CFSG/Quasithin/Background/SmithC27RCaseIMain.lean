module

public import CFSG.Quasithin.Background.SmithC27RCaseI
public import CFSG.Quasithin.Background.SmithC27RLieA6
public import CFSG.Quasithin.Background.SmithC27RLieG2
public import CFSG.Quasithin.Background.SmithC27RTypeRank2
public import CFSG.Quasithin.Background.SmithC27RHat6

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin


variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem ResidueRankTwo.isRadicalParabolic (ht : ResidueRankTwo K V) :
    IsRadicalParabolic (autOn K V) := by
  rcases ht with ⟨n, F, _, _, -, hF, ⟨e⟩, -⟩ | ⟨n, F, _, _, -, hF, ⟨e⟩, -⟩ |
    ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨hhat, -⟩
  · exact (isRadicalParabolic_congr (e.trans Subgroup.topEquiv.symm)).mpr
      (isRadicalParabolic_statedSL 3 (by rw [Nat.card_eq_fintype_card, hF]))
  · exact (isRadicalParabolic_congr (e.trans Subgroup.topEquiv.symm)).mpr
      (isRadicalParabolic_statedSp (by rw [Nat.card_eq_fintype_card, hF]))
  · exact (isRadicalParabolic_congr (e.trans Subgroup.topEquiv.symm)).mpr
      (isRadicalParabolic_quasithinG2 (by rw [Nat.card_eq_fintype_card, hF]) hn)
  · exact (isRadicalParabolic_congr (e.trans Subgroup.topEquiv.symm)).mpr
      isRadicalParabolic_alt6
  · exact (isRadicalParabolic_iff_top _).mpr (isRadicalParabolic_of_isHat_alt6 hhat)

theorem ResidueRankTwo.maxParabolicMaximal (ht : ResidueRankTwo K V) :
    MaxParabolicMaximal (autOn K V) := by
  rcases ht with ⟨n, F, _, _, -, hF, ⟨e⟩, -⟩ | ⟨n, F, _, _, -, hF, ⟨e⟩, -⟩ |
    ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨hhat, -⟩
  · exact (maxParabolicMaximal_congr (e.trans Subgroup.topEquiv.symm)).mpr
      (maxParabolicMaximal_statedSL_three (by rw [Nat.card_eq_fintype_card, hF]))
  · exact (maxParabolicMaximal_congr (e.trans Subgroup.topEquiv.symm)).mpr
      (maxParabolicMaximal_statedSp (by rw [Nat.card_eq_fintype_card, hF]))
  · exact (maxParabolicMaximal_congr (e.trans Subgroup.topEquiv.symm)).mpr
      (maxParabolicMaximal_quasithinG2 (by rw [Nat.card_eq_fintype_card, hF]) hn)
  · exact (maxParabolicMaximal_congr (e.trans Subgroup.topEquiv.symm)).mpr
      maxParabolicMaximal_alt6
  · exact (maxParabolicMaximal_iff_top _).mpr (maxParabolicMaximal_of_isHat_alt6 hhat)

theorem three_of_residueRankTwo (hC132 : ASInputs.AS_C_1_32) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hJ : autOn (thompsonJ R) V ≤ autOn K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) (ht : ResidueRankTwo K V) : C27Three H R M K V :=
  three_of_residueRankTwo_of hC132 h hs hJ hnS ht (ResidueRankTwo.isRankTwoLie2Derived hs ht)
    ht.isRadicalParabolic ht.maxParabolicMaximal fun hb _ htr hmax hO =>
      Or.inr (Or.inr (Or.inl (c27_hat6 h hs hnS hb htr hmax hO hJ)))

theorem three_of_residueTypeI (hC132 : ASInputs.AS_C_1_32) (h : Hyp27 H R M K)
    (hs : StarHyp R K V) (hJ : autOn (thompsonJ R) V ≤ autOn K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R)) (ht : ResidueTypeI K V) : C27Three H R M K V := by
  rcases ht with ht | ht | ht
  · exact (false_of_residueRankOne h hs hJ hnS ht).elim
  · exact three_of_residueRankTwo hC132 h hs hJ hnS ht
  · exact three_of_residueRankThree h hs hJ hnS ht

end CFSG.Quasithin.SmithC27
