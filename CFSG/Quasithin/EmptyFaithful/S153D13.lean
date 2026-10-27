module

public import CFSG.Quasithin.EmptyFaithful.S153D22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Stage15313 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 2 →
      ∀ I : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M I → ¬ CharTwo I

@[expose] def Facts15311All : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → CFSG.Open.pRank 3 Yp = 2 →
      ∀ H : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M H → Facts15311 T M V₁ Yp H

theorem theorem15313_of_inputs
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hcover : AsA36NoOddCover)
    (hFacts : Facts15311All) (h15 : Input15315Two) (h16 : Input15316One) (h17 : Input15317)
    (h18 : Input15318) (h19 : Input15319) (h20 : Input15320) (h21 : Input15321)
    (h23 : Input15323) (h24 : Input15324) : Stage15313 := by
  intro G _ _ T Mc M V₁ V₂ Yp t hyp hrank I hI hchar
  have c0 : Ctx15313 T Mc M V₁ V₂ Yp I t := ⟨hyp, hI, hrank, hchar⟩
  have hF : Facts15311 T M V₁ Yp I := hFacts G T Mc M V₁ V₂ Yp t hyp hrank I hI
  obtain ⟨L, hL⟩ := S153D.lemma_15_3_15_two h15 h37 h38 c0 hF
  have cL : Ctx15313L T Mc M V₁ V₂ Yp I L t := ⟨c0, hF, hL⟩
  have cc : Ctx15316 T Mc M V₁ V₂ Yp I L t :=
    ⟨cL, S153D.lemma_15_3_16 (hC27 G) h16 h37 h38 cL⟩
  have c17 := h17 G T Mc M V₁ V₂ Yp I L t cc
  have n18 := h18 G T Mc M V₁ V₂ Yp I L t cc c17
  have n19 := h19 G T Mc M V₁ V₂ Yp I L t cc c17 n18
  have n20 := h20 G T Mc M V₁ V₂ Yp I L t cc c17 n18 n19
  have n21 := h21 G T Mc M V₁ V₂ Yp I L t cc c17 n18 n19 n20.1 n20.2
  rcases S153D.lemma_15_3_22 hcover cc n18 n19 n20 n21 with h | h | h
  · exact h23 G T Mc M V₁ V₂ Yp I L t cc h
  · exact (h24 G T Mc M V₁ V₂ Yp I L t cc c17).1 h
  · exact (h24 G T Mc M V₁ V₂ Yp I L t cc c17).2 h

end CFSG.Quasithin
