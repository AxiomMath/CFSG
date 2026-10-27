module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Comparison15421Fix
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421Component

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem componentComparison15421_of
    (h56 : AsB56) (hF618 : F6.TheoremF618Cat)
    (hA : F618ComponentInspection) (hD : FixG2Derived) (hE : FixA7Four) (hF : FixTripleA6) :
    ComponentComparison15421 := by
  intro G _ _ I G₁ G₂ T₀ hI htr hT₀ ham _ hV hC hFF hK
  obtain ⟨K, hK⟩ := hK
  have hIV : I ≤ Subgroup.normalizer
      (conjClosure (quasithinOmegaOneCenter T₀) I : Set G) :=
    le_normalizer_conjClosure _ _
  refine C421.not_isPGroup_of_isComponent hV hIV hC hI htr ham hF618 hA h56 hD hE hF hFF hK
    (le_conjClosure _ _) ?_
  intro z hz t ht
  rw [hT₀] at ht
  exact Subgroup.mem_centralizer_iff.mp (L15420.omegaOneCenter_le_center T₀ hz).2 t ht

end CFSG.Quasithin.EmptyFaithfulMultiple
