module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocDefs
public import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
public import CFSG.Quasithin.EmptyFaithful.S1421QNSAlt5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SzSurvLoc

variable {G : Type} [Group G] [Finite G]

theorem survivorLoc_cases_legacyBare {K1 L2 S : Subgroup G} (hc : K1 ∈ cComp (K1 ⊔ S))
    (hn : S ≤ Subgroup.normalizer (K1 : Set G)) (hsurv : F112SurvivorLoc K1 L2 S) :
    (Nat.card (OTwoQuot K1) = 504 ∧ IsSimpleGroup (OTwoQuot K1) ∧
        IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1)) ∨
    (Nat.card (OTwoQuot K1) = 60 ∧ IsSimpleGroup (OTwoQuot K1) ∧
        IsQ8D8 ↥(pCoreOf 2 K1)) := by
  rcases hsurv with h4 | h10 | h11
  · obtain ⟨-, hL3, hQ, -⟩ := h4
    left
    refine ⟨?_, S1421NS.isSimpleGroup_of_isL2Quot (by norm_num) hL3, hQ⟩
    rw [hL3.card (by norm_num)]
    norm_num
  · obtain ⟨hL2, hQ, -⟩ := h10
    right
    refine ⟨?_, S1421NS.isSimpleGroup_of_isL2Quot (by norm_num) hL2, hQ⟩
    rw [hL2.card (by norm_num)]
    norm_num
  · obtain ⟨⟨e⟩, hQ, -⟩ := h11
    obtain ⟨e'⟩ := S1421NS.oTwoQuot_equiv_alt5 hn (ne_bot_of_mem_cComp hc)
      (perfect_of_mem_cComp hc) e
    right
    refine ⟨?_, e'.isSimpleGroup, hQ⟩
    rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide

end SzSurvLoc

end CFSG.Quasithin
