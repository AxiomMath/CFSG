module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoLnA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_s1_two_ln (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5)
    (hLm : IsLn ↥(lBar V₀ V hV L) m 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  obtain ⟨hK, ⟨L₀, hI, hL₀⟩, hsig⟩ :=
    s16e_two_ln_mbar_structure D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hm3 hm5 hLm
      hsum
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have htop : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL hs
  have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
    rw [← htop]
    exact hsum
  exact ⟨hK, ⟨L₀, hI, Or.inr (Or.inl ⟨m, hm3, hm5, hL₀, hLm, hsum'⟩)⟩, hsig⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
