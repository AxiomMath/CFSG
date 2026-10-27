module

public import CFSG.Quasithin.EmptyFaithful.S151XF
public import CFSG.Quasithin.Background.FLcSL

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem s1516_le_mZ1516 {T Mc M Z₁ : Subgroup G} (h18 : Lemma15118Concl T Mc M Z₁) :
    s1516 T Z₁ ≤ mZ1516 Mc Z₁ :=
  le_inf (s1516_le_g1 T Z₁) ((s1516_le T Z₁).trans (le_sup_right.trans h18.seven.1.1.2))

theorem isParabolic2_mZ1516_inf {T Mc M Z₁ L : Subgroup G} (h18 : Lemma15118Concl T Mc M Z₁)
    (hL : IsL1520 T Mc Z₁ L) (hlist : ListC15120 L) :
    IsParabolic2 L (mZ1516 Mc Z₁ ⊓ L) := by
  have hSyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow h18.four hL
  refine ⟨inf_le_right, s1516 T Z₁ ⊓ L, hSyl, fun x hx => ?_⟩
  have hxS : x ∈ s1516 T Z₁ ⊓ L := by
    rcases hlist with h | h
    · exact FLc.normalizer_inf_le_of_isPSL (by norm_num) h hSyl hx
    · exact FLc.normalizer_inf_le_of_isPSL (by norm_num) h hSyl hx
  exact ⟨s1516_le_mZ1516 h18 hxS.1, hxS.2⟩

theorem input15120L45_holds : Input15120L45 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc _ hlist
  refine ⟨hlist, isParabolic2_mZ1516_inf hc.h18 hc.hL hlist, fun h => hc.hL.not_le ?_⟩
  calc L = mZ1516 Mc Z₁ ⊓ L := h.symm
    _ ≤ mZ1516 Mc Z₁ := inf_le_left

end CFSG.Quasithin
