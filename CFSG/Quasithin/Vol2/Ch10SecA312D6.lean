module

public import CFSG.Quasithin.Vol2.Ch10SecA312D3
public import CFSG.Quasithin.Vol2.Ch10SecA312D4
public import CFSG.Quasithin.Vol2.Ch10SecA312D5
public import CFSG.Quasithin.Vol2.Ch10SecA312C11

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem a312PairCentStruct_holds :
    A312PairCentStruct := by
  intro X _ _ hq _ _ T hT B₁ hB₁ B₂ hB₂ hne₁ _ hne hN₁ hN₂ hc ⟨e⟩ hs
  have hB := perfect_of_mem_cComp (show B₁ ∈ cComp (B₁ ⊔ T) from hB₁)
  have hc₁ : ⁅B₁, B₂⁆ ≤ B₁ := hc.trans (inf_le_left.trans (Subgroup.map_subtype_le _))
  rcases hs with h | ⟨f, -, hf, -⟩ | ⟨hA, p, hp, hL, -, h8, -, -⟩ | ⟨s, p, hp, hp3, hS, hL, -⟩ |
      h | ⟨h, hL⟩ | ⟨h, hL⟩ | ⟨h, h11, hL⟩
  · exact A312D.false_of_rank2 hq h.2.1 hT hB₁ hB₂ hne₁ hne hN₁ hN₂ hc₁
  · exact A312D.false_of_rank2 hq (H13.isRank2LieChar2_of_is2F4 hf) hT hB₁ hB₂ hne₁ hne hN₁ hN₂
      hc₁
  · exact A312D.case8s hB hc e hA hp hL h8
  · exact A312D.case9s hB hc e hp hp3 hS hL
  · exact A312D.case16s hB hc e h
  · exact A312D.case18s hB hc e h hL
  · exact A312D.case19s hB hc e h hL
  · exact A312D.case20s hB hc e h h11 hL

theorem a312PairCent_holds
    (hList : Vol2Native.A312ListFactsCat) : A312PairCent :=
  a312PairCent_of hList a312PairCentStruct_holds

end CFSG.Quasithin.Vol2.Ch10
