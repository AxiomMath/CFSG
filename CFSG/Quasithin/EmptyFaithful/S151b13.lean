module

public import CFSG.Quasithin.EmptyFaithful.S151b13Three
public import CFSG.Quasithin.EmptyFaithful.S151bRankBound

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem lemma15113Three_of_cases151b {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (h157 : Lemma1517Concl T Mc M) (h158 : Lemma1518Concl T Mc M)
    (h159 : Lemma1519Concl T Mc M) (hred : IsTwoReducedIn M (V154 T Mc M))
    (h110 : Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) 3 →
      Nonempty (↥(autOn M (V154 T Mc M)) ≃* S152N.W3))
    (h5 : ∀ hV : IsElemAbelian 2 (V154 T Mc M),
      Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) 5 →
      ∀ E : Subgroup (MulAut (IntMod (V154 T Mc M) hV)), E ≤ autI hV T → IsElemAbelian2 E →
        Nat.card E ≤ 4) :
    Lemma15113Three T Mc M := by
  have hV : IsElemAbelian 2 (V154 T Mc M) := hred.2.2.1
  have hTM : T ≤ M := hM.1.1.2
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hVT : V154 T Mc M ≤ T := (V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ h hM.1.1).2
  have hJ : thompsonJ T ≤ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_centralizer_of_commutator_eq_bot h159.one_commute
  by_cases hc3 : Case1517Three M (V154 T Mc M) (mBar0 T Mc M)
  · exact Or.inr hc3
  · refine Or.inl fun A hA hA1 => ?_
    have hq : qhatOn M (V154 T Mc M) = 2 ∧ qOn M (V154 T Mc M) = 2 := by
      rcases h158 with h1 | ⟨h3, -⟩
      · exact h1
      · exact absurd h3 hc3
    have hqhat : qhatOf (autI hV M) = ((2 : ℚ) : WithTop ℚ) := by
      rw [← qhatOn_eq_qhatOf151b hV, hq.1]
      norm_cast
    have hq' : qOf (autI hV M) = ((2 : ℚ) : WithTop ℚ) := by
      rw [← qOn_eq_qOf151b hV, hq.2]
      norm_cast
    have hrank := rank_bound_of_cases151b h hM hV hred h157.1 hc3 h110 (h5 hV)
    obtain ⟨hcard, hmem⟩ := corank_one_mem_QhatStar151b hV hVT hTM hMN hJ hqhat hq' hrank hA hA1
    exact ⟨hcard, (mem_QhatStarOn_iff151b hV _).mpr hmem⟩

end CFSG.Quasithin
