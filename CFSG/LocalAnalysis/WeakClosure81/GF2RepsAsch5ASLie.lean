module

public import CFSG.Quasithin.Background.RonanE114L2Main
public import CFSG.Quasithin.Vol2.Ch11SecOE8K
public import CFSG.Quasithin.Vol2.Ch11SecOE8V
public import CFSG.Quasithin.Vol2.Ch11SecOE9Q

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_lie_noSQ {T : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (h : IsPSL 2 2 n ↥(CFSG.generalizedFitting G) ∨ IsPSU 3 2 n ↥(CFSG.generalizedFitting G) ∨
      IsPSL 3 2 n ↥(CFSG.generalizedFitting G) ∨ IsPSp4 2 n ↥(CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ n := by
  rcases h with h | h | h | h
  · exact (SecE3.nParam_eq_of_isPSL22 h hFs hT hFT).le
  · exact (SecE3.Lie3.nParam_eq_of_isPSU3 h hFs hT hFT).le
  · by_cases htw : E2.IsDiagramNontrivial T (CFSG.generalizedFitting G)
        (T ⊓ CFSG.generalizedFitting G)
    · exact SecE3.Lie3.nParam_le_of_isPSL3_of_twisted hn h hFs hT hFT htw
    · exact SecE3.Lie3.nParam_le_of_isPSL3_of_untwisted hn h hT hFT htw
  · by_cases htw : E2.IsDiagramNontrivial T (CFSG.generalizedFitting G)
        (T ⊓ CFSG.generalizedFitting G)
    · exact SecE3.Lie3.nParam_le_of_isPSp4_of_twisted h hFs hT hFT htw
    · exact SecE3.Lie3.nParam_le_of_isPSp4_of_untwisted h hT hFT htw

theorem nParam_le_one_of_isPSL2_noSQ
    {T : Subgroup G}
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 < p ^ e) (hF : IsPSL 2 p e ↥(CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  by_cases he : e ≤ 2
  · have he1 : 1 ≤ e := by
      by_contra h
      obtain rfl : e = 0 := by omega
      simp at h5
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
        exact E2.E22N.nParam_le_one_of_alt6 (RonanE114.isAlt6_of_isPSL2_nine hF)
      · have hp5 : 5 ≤ p := by
          have := hp.two_le
          have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
          omega
        exact SecU1.nParam_le_one_of_setting SecU1.torusMember_holds SecU1.componentMember_holds
          (SecU1.setting_of_psl2_sq hp hp5 hFs hF hT.1 hFT)
  · exact RonanE114.L2.nParam_le_one_of_psl2_pow hp hp2 (by omega) hFs hF hT.1 hFT

end CFSG.LocalAnalysis.WeakClosure81

end
