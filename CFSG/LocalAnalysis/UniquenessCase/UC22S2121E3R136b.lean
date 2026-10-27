module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3Cartan
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R78p3
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusPure
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankNT1
import CFSG.LocalAnalysis.UniquenessCase.UC1K337
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xn
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3OrB
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3P3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3Types

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3_two_members_r847E3
    (hSE : StronglyEmbeddedFive) (hThin : PartTwo.ThinList13) (hS : Standing G) (S : Setup G)
    (hS13 : PartTwo.Setting13 (PartTwo.Three.dataOfSetup hS S))
    (hSig : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S))
    (h78 : R7_8R3p3 (PartTwo.Three.dataOfSetup hS S)) {p : ℕ}
    (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) {B : Subgroup G}
    (hB : F13.Case136b (PartTwo.Three.dataOfSetup hS S) p B) {L K : Subgroup G}
    (hL : L ∈ calC S.M) (hK : K ∈ calC S.M) (hne : barImage S.M L ≠ barImage S.M K)
    (hpL : p ∣ Nat.card (barImage S.M L)) (hpK : p ∣ Nat.card (barImage S.M K))
    (sL : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n))
    (sK : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 K) n ∨ IsU3 (Bar2 K) n))
    (hK1 : CFSG.Open.pRank p K ≤ 1)
    (hsum : CFSG.Open.pRank p L + CFSG.Open.pRank p K + CFSG.Open.pRank p (F13.Sp S.M p) = 3) :
    ∃ n, IsPowTwo n ∧ p ∣ 2 ^ n + 1 ∧ IsL2 (Bar2 K) n ∧
      ((IsL2 (Bar2 L) n ∧ CFSG.Open.pRank p (F13.Sp S.M p) = 1) ∨
        (IsU3 (Bar2 L) n ∧ CFSG.Open.pRank p (F13.Sp S.M p) = 0)) := by
  obtain ⟨hpp, hp2⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  have hS1 : CFSG.Open.pRank p (F13.Sp S.M p) ≤ 1 := hS13.hyp131.smallS p hp
  have hoK : 1 ≤ CFSG.Open.pRank p K := by
    rw [← PartTwo.s13_pRank_barImage hpp hp2 (PartTwo.s13_le_of_mem_calC hK)]
    exact PartTwo.s13_one_le_pRank_of_dvd _ hpp hpK
  obtain ⟨m, hm, hY⟩ := sK
  by_cases hL1 : CFSG.Open.pRank p L ≤ 1
  ·
    have h1 : 1 ≤ CFSG.Open.pRank p (F13.Sp S.M p) := by omega
    obtain ⟨n, hn, hX⟩ := sL
    rcases eq_or_ne p 3 with rfl | hp3
    · obtain ⟨y, hyN, hy, hyc⟩ := uc22s2121e3_exists_elem_Sp hThin hS13 hpp hB h1
      exact (uc22s2121e3_false_p3 hThin hS13 hSig h78 hp hB hL hK hne ⟨n, hn, hX⟩ ⟨m, hm, hY⟩
        y.2 hyN hy (hyc _ (PartTwo.s13_mem_compsP.mpr ⟨PartTwo.s13_barImage_isComponent hL, hpL⟩))
        (hyc _ (PartTwo.s13_mem_compsP.mpr ⟨PartTwo.s13_barImage_isComponent hK, hpK⟩))).elim
    have hp5 := hpp.five_le_of_ne_two_of_ne_three hp2 hp3
    obtain ⟨hL2, hpn⟩ := uc22s2121e3_isL2_of_Sp_r847E3 hSE hThin hS S hS13 hSig h847T h847S hp hp5
      hB h1 hL hK hne hpL hpK hn hX hm hY
    obtain ⟨hK2, hpm⟩ := uc22s2121e3_isL2_of_Sp_r847E3 hSE hThin hS S hS13 hSig h847T h847S hp hp5
      hB h1 hK hL hne.symm hpK hpL hm hY hn (Or.inl hL2)
    haveI : Fact p.Prime := ⟨hpp⟩
    rw [← (InS3.k337_holds p hpp hp2 n m hn hm).2.1 (S15.nt1_pow_eq_neg_one hpn)
      (S15.nt1_pow_eq_neg_one hpm)] at hK2
    exact ⟨n, hn, hpn, hK2, Or.inl ⟨hL2, by omega⟩⟩
  ·
    obtain ⟨⟨n, hn, hU, hpn⟩, -⟩ :=
      (uc22s2121e3_pRank_le_of_mem_calC hS13.hyp131 hpp hp2 hL).resolve_left hL1
    have hp5 := hpp.five_le_of_ne_two_of_ne_three hp2
      (uc22s13xn_three_lt hn (PartTwo.s13_two_le_of_isU3 hU) hpp hpn).ne'
    exact ⟨n, hn, hpn, uc22s2121e3_isL2_of_isU3_r847E3 hSE hThin hS S hS13 hSig h847T h847S hp hp5
      hB hL hK hne hn hU hpn hm hY hpK, Or.inr ⟨hU, by omega⟩⟩

theorem uc22s2121e3_r136b_r847E3 (hSE : StronglyEmbeddedFive)
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (hS : Standing G)
    (S : Setup G) (hS13 : PartTwo.Setting13 (PartTwo.Three.dataOfSetup hS S))
    (hSig : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h847T : R847E3Thin (PartTwo.Three.dataOfSetup hS S))
    (h847S : R847E3SU3 (PartTwo.Three.dataOfSetup hS S))
    (h78 : R7_8R3p3 (PartTwo.Three.dataOfSetup hS S))
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (hshape : ∀ L ∈ calC S.M, ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n)) {p : ℕ}
    (hp : p ∈ (PartTwo.Three.dataOfSetup hS S).sig) {B : Subgroup G}
    (hB : F13.Case136b (PartTwo.Three.dataOfSetup hS S) p B) (hBab : IsMulCommutative B) :
    ∃ (L K : Subgroup G) (n : ℕ), L ∈ calC S.M ∧ K ∈ calC S.M ∧
      barImage S.M L ≠ barImage S.M K ∧
      (∀ J : Subgroup (Bar2 S.M), CFSG.IsComponent J →
        J = barImage S.M L ∨ J = barImage S.M K) ∧
      p ∣ Nat.card (barImage S.M L) ∧ p ∣ Nat.card (barImage S.M K) ∧
      IsPowTwo n ∧ p ∣ 2 ^ n + 1 ∧ IsL2 (Bar2 K) n ∧
      ((IsL2 (Bar2 L) n ∧ CFSG.Open.pRank p (F13.Sp S.M p) = 1) ∨
        (IsU3 (Bar2 L) n ∧ CFSG.Open.pRank p (F13.Sp S.M p) = 0)) ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card B → r ∣ 2 ^ n - 1 := by
  classical
  obtain ⟨hpp, hp2⟩ := (PartTwo.Three.dataOfSetup hS S).sig_prime p hp
  have h3 : CFSG.Open.pRank p S.M = 3 := uc22s2121e3_pRank_eq_three hSig hS.rank hp
  have hsum : CFSG.Open.pRank p S.M = ∑ J ∈ PartTwo.s13_compsP (Bar2 S.M) p,
      CFSG.Open.pRank p J + CFSG.Open.pRank p (F13.Sp S.M p) :=
    uc22s2121e3_pRank_eq_sum hThin hCyc hS13 hSig hp
  have hS1 : CFSG.Open.pRank p (F13.Sp S.M p) ≤ 1 := hS13.hyp131.smallS p hp
  generalize hC : PartTwo.s13_compsP (Bar2 S.M) p = C at hsum
  have hcomp : ∀ J ∈ C, ∃ L ∈ calC S.M, barImage S.M L = J ∧ p ∣ Nat.card J ∧
      CFSG.Open.pRank p J = CFSG.Open.pRank p L := by
    intro J hJ
    rw [← hC] at hJ
    obtain ⟨hJc, hd⟩ := PartTwo.s13_mem_compsP.mp hJ
    obtain ⟨L, hL, rfl⟩ := PartTwo.s13_exists_calC_of_component S.M hJc
    exact ⟨L, hL, rfl, hd, PartTwo.s13_pRank_barImage hpp hp2 (PartTwo.s13_le_of_mem_calC hL)⟩
  obtain ⟨L, K, hL, hK, hne, hall, hpL, hpK, hK1, hsum'⟩ : ∃ L K : Subgroup G,
      L ∈ calC S.M ∧ K ∈ calC S.M ∧ barImage S.M L ≠ barImage S.M K ∧
      (∀ J : Subgroup (Bar2 S.M), CFSG.IsComponent J →
        J = barImage S.M L ∨ J = barImage S.M K) ∧
      p ∣ Nat.card (barImage S.M L) ∧ p ∣ Nat.card (barImage S.M K) ∧
      CFSG.Open.pRank p K ≤ 1 ∧
      CFSG.Open.pRank p L + CFSG.Open.pRank p K + CFSG.Open.pRank p (F13.Sp S.M p) = 3 := by
    rcases Nat.lt_or_ge 2 C.card with hc | hc
    ·
      exfalso
      obtain ⟨J₁, hJ₁, J₂, hJ₂, J₃, hJ₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hc
      obtain ⟨L₁, hL₁, rfl, -⟩ := hcomp J₁ hJ₁
      obtain ⟨L₂, hL₂, rfl, -⟩ := hcomp J₂ hJ₂
      obtain ⟨L₃, hL₃, rfl, -⟩ := hcomp J₃ hJ₃
      exact uc22ine229_s13xo_false_p3 hThin hS13 h78 h82 hB hL₁ hL₂ hL₃ h12 h13 h23
        (hshape L₁ hL₁) (hshape L₂ hL₂) (hshape L₃ hL₃)
    rcases Nat.lt_or_ge 1 C.card with hc' | hc'
    ·
      obtain ⟨J₁, J₂, h12, hJ⟩ := Finset.card_eq_two.mp (show C.card = 2 by omega)
      rw [hJ, Finset.sum_pair h12] at hsum
      obtain ⟨L, hL, rfl, hpL, hrL⟩ :=
        hcomp J₁ (by rw [hJ]; exact Finset.mem_insert_self _ _)
      obtain ⟨K, hK, rfl, hpK, hrK⟩ :=
        hcomp J₂ (by rw [hJ]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hall : ∀ J : Subgroup (Bar2 S.M), CFSG.IsComponent J →
          J = barImage S.M L ∨ J = barImage S.M K := by
        intro J hJc
        by_contra hJn
        obtain ⟨hJL, hJK⟩ := not_or.mp hJn
        obtain ⟨X, hX, rfl⟩ := PartTwo.s13_exists_calC_of_component S.M hJc
        exact uc22ine229_s13xo_false_p3 hThin hS13 h78 h82 hB hL hK hX h12 (Ne.symm hJL)
          (Ne.symm hJK) (hshape L hL) (hshape K hK) (hshape X hX)
      have hoL := PartTwo.s13_one_le_pRank_of_dvd _ hpp hpL
      have hoK := PartTwo.s13_one_le_pRank_of_dvd _ hpp hpK
      by_cases hK1 : CFSG.Open.pRank p K ≤ 1
      · exact ⟨L, K, hL, hK, h12, hall, hpL, hpK, hK1, by omega⟩
      · exact ⟨K, L, hK, hL, h12.symm, fun J hJ => (hall J hJ).symm, hpK, hpL, by omega,
          by omega⟩
    exfalso
    rcases Nat.lt_or_ge 0 C.card with hc'' | hc''
    · obtain ⟨J, hJ⟩ := Finset.card_eq_one.mp (show C.card = 1 by omega)
      rw [hJ, Finset.sum_singleton] at hsum
      obtain ⟨L, hL, rfl, hpL, hrL⟩ := hcomp J (by rw [hJ]; exact Finset.mem_singleton_self _)
      obtain ⟨⟨n, hn, hU, hpn⟩, hL2⟩ :=
        (uc22s2121e3_pRank_le_of_mem_calC hS13.hyp131 hpp hp2 hL).resolve_left (by omega)
      exact uc22s2121e3_not_cartan_of_Sp_r847E3 hSE hThin hS S hS13 hSig h847T h847S hp
        (hpp.five_le_of_ne_two_of_ne_three hp2
          (uc22s13xn_three_lt hn (PartTwo.s13_two_le_of_isU3 hU) hpp hpn).ne')
        hB (by omega) hL hpL hn (Or.inr hU) (Or.inr ⟨hU, hpn⟩)
    · rw [Finset.card_eq_zero.mp (show C.card = 0 by omega), Finset.sum_empty] at hsum
      omega
  obtain ⟨n, hn, hpn, hK2, hLs⟩ := uc22s2121e3_two_members_r847E3 hSE hThin hS S hS13 hSig h847T
    h847S h78 hp hB hL hK hne hpL hpK (hshape L hL) (hshape K hK) hK1 hsum'
  refine ⟨L, K, n, hL, hK, hne, hall, hpL, hpK, hn, hpn, hK2, hLs, fun r hr hrB => ?_⟩
  by_contra hr1
  exact uc22s2121e3_false_of_not_dvd_r847E3 hSE hS S h847T h847S hThin hS13 hp
    (hSig.sig1_sp p (hS13.sig_eq ▸ hp)) hB hBab hL hK hne hn (hLs.imp And.left And.left) hK2 hpn
    hr hrB hr1

end CFSG.LocalAnalysis.UniquenessCase.UC22
