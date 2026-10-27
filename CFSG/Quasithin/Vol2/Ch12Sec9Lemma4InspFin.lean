module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Red
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Insp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem g112Inspect1294_of
    (hSeven : G112ConclSeven) : G112Inspect1294 := by
  intro V _ _ _ B Γ v₁ W X X₀ hG111 hsqtk hfix Q _ ψ hQ hψΓ hΓψ hne
  have := L1294I.finite_glv (V := V)
  have hA : ¬ IsList1293Two Q := fun h2 => by
    obtain ⟨hbig, h7, h3⟩ := L1294Q.list2 h2 hne
    exact L1294I.false_of_list2 hG111 hfix hψΓ hΓψ hne hbig h7 h3
  refine ⟨hA, fun S Lt hS hLt hSLt hLt3 => ?_⟩
  obtain ⟨e⟩ := hLt3
  obtain ⟨k, hk⟩ := L1294I.card_of_quot_sl3 e
  exact L1294I.of_list3 hSeven hG111 hsqtk hfix hψΓ hΓψ hne
    (L1294Q.list3 (hQ.resolve_left hA) hne) hS hLt hSLt hk

end CFSG.Quasithin.H13
