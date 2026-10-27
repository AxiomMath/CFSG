module

public import CFSG.Quasithin.Recognition.Stroth.SliceSzUReduction
public import CFSG.Quasithin.H13.F112DSL2Slices
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceSolv
public import CFSG.Quasithin.Vol2.GoldschmidtF112SliceDS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.Stroth

theorem dsAConc_szU_L2_of_parts (hSzL2 : IdSzL2) (hU3L2 : IdU3L2) (hF4 : Y9TwistedF4)
    (hU5 : Y9U54) {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VSzBig L1 ∨ VU3Big L1) (hb2 : VBig L2) (h2 : VL2 L2) :
    F112ConclWith F112ListA L1 L2 S := by
  rcases h1 with ⟨a, ha, ⟨e⟩⟩ | h1U3
  · obtain ⟨hq2, hA⟩ := hSzL2 G L1 L2 S a hF ha ⟨e⟩ hb2 h2
    obtain ⟨hZ, hc1, hc2, hPerf⟩ := hF4 G L1 L2 S a hF ha ⟨e⟩ hq2 hA
    have hA' : F112ListA L1 L2 S := by
      unfold F112ListA
      dsimp only
      iterate 4 right
      left
      exact ⟨a, ha, hA, ⟨e⟩, hc1, hq2, hc2⟩
    exact ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, fun _ => hZ, hA', Or.inl hPerf⟩
  · obtain ⟨⟨F, hField, hFin, hcard4, hSU4⟩, hq2, hA⟩ := hU3L2 G L1 L2 S hF h1U3 hb2 h2
    obtain ⟨hZ, hs, hc2, hPerf⟩ := hU5 G L1 L2 S hF ⟨F, hField, hFin, hcard4, hSU4⟩ hq2 hA
    have hA' : F112ListA L1 L2 S := by
      unfold F112ListA
      dsimp only
      iterate 6 right
      exact ⟨hA, ⟨F, hField, hFin, hcard4, hSU4⟩, hs, hq2, hc2⟩
    exact ⟨L1, L2, Or.inl ⟨rfl, rfl⟩, fun _ => hZ, hA', Or.inl hPerf⟩

theorem dsAL2_of_parts (hL2 : F112SliceBigL2 DSAConc) (hSzL2 : IdSzL2) (hU3L2 : IdU3L2)
    (hF4 : Y9TwistedF4) (hU5 : Y9U54) : DSAL2Statement := by
  intro G _ _ L1 L2 S hyp hq hS hns1 hns2 hL
  have hF : F112Hyp L1 L2 S := ⟨hyp, hq, hS⟩
  have hb1 : VBig L1 := vBig_of_not_isSolvable hns1
  have hb2 : VBig L2 := vBig_of_not_isSolvable hns2
  show F112ConclWith F112ListA L1 L2 S
  rcases hL with h1 | h2
  · rcases vBig_trichotomy hF.1.h2 hb2 with h2 | h2 | h2
    · exact hL2 G L1 L2 S hF ⟨⟨hb1, hb2⟩, h1, h2⟩
    · exact F112ConclWith.symm
        (dsAConc_szU_L2_of_parts hSzL2 hU3L2 hF4 hU5 hF.symm (Or.inl h2) hb1 h1)
    · exact F112ConclWith.symm
        (dsAConc_szU_L2_of_parts hSzL2 hU3L2 hF4 hU5 hF.symm (Or.inr h2) hb1 h1)
  · rcases vBig_trichotomy hF.1.h1 hb1 with h1 | h1 | h1
    · exact hL2 G L1 L2 S hF ⟨⟨hb1, hb2⟩, h1, h2⟩
    · exact dsAConc_szU_L2_of_parts hSzL2 hU3L2 hF4 hU5 hF (Or.inl h1) hb2 h2
    · exact dsAConc_szU_L2_of_parts hSzL2 hU3L2 hF4 hU5 hF (Or.inr h1) hb2 h2

end CFSG.Quasithin.H13
