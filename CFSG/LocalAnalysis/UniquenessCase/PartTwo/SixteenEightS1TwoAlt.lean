module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoAltA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_s1_two_alt (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn5 : 5 ≤ n) (hn11 : n ≤ 11) (hn6 : n ≠ 6)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have hwstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL hs
  have hK := s16e_two_alt_kbar D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hn5 hn11 hn6
    hA hsum
  have hsig := s16e_two_alt_sig D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hn5 hn11 hn6
    hA hsum
  obtain ⟨L₀, hdir, hSym⟩ :=
    s16e_two_alt_direct D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hn5 hn11 hn6 hA hsum
  have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
    rw [← hwstar]
    exact hsum
  exact ⟨hK, ⟨⟨L₀, hdir, Or.inl ⟨n, hn5, hn11, hSym, hA, hsum'⟩⟩, hsig⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
