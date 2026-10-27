module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BProper
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BSp4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BHat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BSeven
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4BL45

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223P4

namespace B

theorem lnQuot_of_not_caseG
    (hθ : ThetaEqComponent) (hcover : AsA36NoOddCover) (kR : Input21Rank) (kL : ThreeRankBlocks)
    (kP : Input21ProperRank) (kB : SolvOvergroupsInBorel)
    {G : Type} [Group G] [Finite G] {T Mc M H : Subgroup G}
    {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}
    (c : P4Ctx T Mc M H B₀ I X)
    (hg : ¬ SBc17.C27SL3 I (P4R M I) (M ⊓ I) X (P4V M I X)) :
    IsLnTwoQuot X 4 ∨ IsLnTwoQuot X 5 := by
  have facts6 : IsAltBlockType X 6 → P4Fact T Mc M H B₀ I X := fun h =>
    c.facts hθ (kR G X (Or.inl h)) (Or.inl h)
  rcases c.cases with h | h | h | h | h | h | h | h | h | h | h
  · exact (c.noChi X h.1).elim
  · exact (c.noChi X h.1).elim
  · exact (c.noChi X h.1).elim
  · exact (c.noChi X h.1).elim
  ·
    obtain ⟨⟨n, α, h5, h8, hshort, hα, -⟩, -⟩ := h
    interval_cases n
    · exact (c.noChi X ⟨isBlock2_of_short c hshort, Or.inr ⟨5, by decide,
        (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 5)).mpr ⟨α, hα⟩⟩⟩).elim
    · exact (not_A6_G2 kP c (facts6 ⟨hshort, α, hα⟩) (Or.inl ⟨hshort, α, hα⟩)).elim
    · exact (c.noChi X ⟨isBlock2_of_short c hshort, Or.inr ⟨7, by decide,
        (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 7)).mpr ⟨α, hα⟩⟩⟩).elim
    · exact Or.inl (S153D.isLnTwoQuot_four_of_altBlockTypeWith_eight hα)
  ·
    obtain ⟨hHat, hidx, -⟩ := h
    have f := c.facts hθ (kR G X (Or.inr (Or.inr (Or.inl hHat)))) (Or.inr (Or.inr (Or.inl hHat)))
    exact (not_Hat6 c f hHat hidx).elim
  ·
    obtain ⟨hExc, hidx⟩ := h
    have f := c.facts hθ (kR G X (Or.inr (Or.inr (Or.inr (Or.inr hExc)))))
      (Or.inr (Or.inr (Or.inr (Or.inl hExc))))
    exact (not_ExcA7 c f hExc hidx).elim
  ·
    obtain ⟨hA6 | hSp4, hpar⟩ := h
    · exact (not_A6_G2 kP c (facts6 hA6) (Or.inl hA6)).elim
    · have hSp := S153D.isSp4Quot_of_isSp4Block hSp4
      have f := c.facts hθ ((kL G X).2.2 (Or.inl hSp))
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSp))))))
      exact (not_Sp4 kB c f hSp hpar.1).elim
  ·
    obtain ⟨hG2, -, -⟩ := h
    have f := c.facts hθ (kR G X (Or.inr (Or.inl hG2)))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hG2)))))
    exact (not_A6_G2 kP c f (Or.inr hG2)).elim
  · exact (hg h).elim
  ·
    obtain ⟨h45, -, hB⟩ := h
    exact lnQuot_of_autOn hcover c h45 hB

end B

end S15223P4

end CFSG.Quasithin
