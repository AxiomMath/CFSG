module

public import CFSG.RankThree.PartTwo.Sec16.Item168StepsProofTwo
public import CFSG.RankThree.PartTwo.Sec16.Item166Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof166TwoPow

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem omega166_of_item165 (h : Sec17Std G A c L Y₀) (h165 : Item165 A (lB A) L)
    (hL : IsL3TwoPow L) : Omega166 A Y₀ :=
  fun _ Z _ _ _ hZ => h165 hL Y₀ h.mem_y0Star Z hZ.prop

theorem ctr166_of_item165 (h : Sec17Std G A c L Y₀) (h165 : Item165 A (lB A) L)
    (hL : IsL3TwoPow L) : Ctr166 A Y₀ :=
  fun X hX _ _ _ => h165 hL Y₀ h.mem_y0Star X hX.prop

theorem two168Out_of_item165 (h : Sec17Std G A c L Y₀) (h165 : Item165 A (lB A) L)
    (hL : IsL3TwoPow L) : Two168Out A Y₀ := by
  intro V hV Y hY hVY
  exact absurd (hVY.trans (h165 hL Y₀ h.mem_y0Star Y hY))
    (Proof168Steps.not_le_M_of_mem_omega168 h hV)

end Proof166TwoPow

@[expose] def Step166OmegaNot2n : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ IsL3TwoPow L → Omega166 A Y₀

@[expose] def Step166CtrNot2n : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ IsL3TwoPow L → Ctr166 A Y₀

theorem step166Omega_of_not2n (h165 : Item165S17) (h : Step166OmegaNot2n) : Step166Omega := by
  intro G _ _ A c L Y₀ hs
  by_cases hL : IsL3TwoPow L
  · exact Proof166TwoPow.omega166_of_item165 hs (h165 G A c L Y₀ hs) hL
  · exact h G A c L Y₀ hs hL

theorem step166Ctr_of_not2n (h165 : Item165S17) (h : Step166CtrNot2n) : Step166Ctr := by
  intro G _ _ A c L Y₀ hs
  by_cases hL : IsL3TwoPow L
  · exact Proof166TwoPow.ctr166_of_item165 hs (h165 G A c L Y₀ hs) hL
  · exact h G A c L Y₀ hs hL

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec16

@[expose] def Step168TwoOutNot2n : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ IsL3TwoPow L → Two168Out A Y₀

theorem step168TwoOut_of_not2n (h165 : Item165S17) (h : Step168TwoOutNot2n) : Step168TwoOut := by
  intro G _ _ A c L Y₀ hs
  by_cases hL : IsL3TwoPow L
  · exact Proof166TwoPow.two168Out_of_item165 hs (h165 G A c L Y₀ hs) hL
  · exact h G A c L Y₀ hs hL

end CFSG.RankThree.PartTwo.Sec17
