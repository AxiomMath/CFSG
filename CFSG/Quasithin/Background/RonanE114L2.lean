module

public import CFSG.Quasithin.Background.RonanE114A7
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IF
public import CFSG.Quasithin.Vol2.Ch11SecU1Set
public import CFSG.Sporadic.Recognition.JankoWongPSLNine

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11

theorem isAlt6_of_isPSL2_nine {X : Type} [Group X] (h : IsPSL 2 3 2 X) : IsAlt 6 X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨f⟩ := CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine
    (F := K) (by rw [hK]; norm_num)
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans f⟩

theorem two_dvd_card_of_isPSL2 {X : Type} [Group X] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (h : IsPSL 2 p e X) : 2 ∣ Nat.card X := by
  obtain ⟨-, K, _, _, hK, ⟨f⟩⟩ := h
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, e, hp, hp.odd_of_ne_two hp2, he, hK⟩
  have hPSL : Nat.card (CFSG.GorensteinWalter.PSL2 K) =
      Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) :=
    Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).toEquiv
  rw [Nat.card_congr f.toEquiv, ← hPSL]
  exact CFSG.Walter.Suzuki.two_dvd_card_psl2 K hodd

variable {G : Type} [Group G] [Finite G]

theorem nParam_eq_one_of_isPSL2_of_le_two
    {T : Subgroup G} (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 < p ^ e) (he : e ≤ 2) (hF : IsPSL 2 p e (ASInputs.FStar G)) :
    E1.nParam (⊤ : Subgroup G) = 1 := by
  have he1 : 1 ≤ e := by
    by_contra h
    obtain rfl : e = 0 := by omega
    simp at h5
  refine le_antisymm ?_ (SecE3.one_le_nParam_of_not_odd
    (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G)
      (two_dvd_card_of_isPSL2 hp hp2 he1 hF)))
  have : Fact p.Prime := ⟨hp⟩
  have hle : p ^ e ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos he
  rcases (by omega : e = 1 ∨ e = 2) with rfl | rfl
  · rw [pow_one] at h5
    have hp7 : 7 ≤ p := by
      have := hp.two_le
      have hp5 : p ≠ 5 := by rintro rfl; omega
      have hp3 : p ≠ 3 := by rintro rfl; omega
      by_contra hlt
      have : p = 2 ∨ p = 3 ∨ p = 5 := by
        have hp6 : p ≠ 4 := by rintro rfl; norm_num at hp
        have hp6' : p ≠ 6 := by rintro rfl; norm_num at hp
        omega
      omega
    exact SecU1.L3I.nParam_le_one_of_psl2_prime_ge_seven hp7 hF
  · by_cases hp3 : p = 3
    · subst hp3
      exact E2.E22N.nParam_le_one_of_alt6 (isAlt6_of_isPSL2_nine hF)
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
        omega
      exact E2.E22N.e114ResRestL2_holds G T hSQ hFs hT hFT ⟨p, hp, by omega, hF⟩

end CFSG.Quasithin.RonanE114
