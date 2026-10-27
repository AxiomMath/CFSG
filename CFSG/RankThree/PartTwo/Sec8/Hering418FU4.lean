module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FU4Alt
public import CFSG.RankThree.PartTwo.Sec8.Hering418R47

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Assembly.RankThreeEven (projSU)

section Main


@[expose] def U4OddInner : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (a b : G) (c : Cfg L K a b),
    K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}) → ∀ k : ℕ, Odd k → 3 ∣ k →
      L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 2 k →
      c.alpha ∈ innBar L → c.beta ∈ innBar L → False

theorem kF418ModelOn47_uFourSix_of_odd (hodd : U4OddInner) :
    KF418ModelOn47 (fun X _ => IsUFourSix X) := by
  intro G _ _ L hL hl h47 a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
  exfalso
  obtain ⟨k, hk, h3k, ⟨e⟩⟩ := hl
  have hk3 : 3 ≤ k := Nat.le_of_dvd (by omega) h3k
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact habz (Subgroup.one_mem _)
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hαI : c.alpha ∈ innBar L := by
    by_contra h
    exact not_alt47 hk3 e (h47 a haord ⟨haN, h⟩)
  have hβI : c.beta ∈ innBar L := by
    by_contra h
    exact not_alt47 hk3 e (h47 b hbord ⟨hbN, h⟩)
  rcases Nat.even_or_odd k with he | ho
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hbound := bound_inner_of_pRank (Sec4.quotientCenterCongr e)
      (Sec4.HeringUnitary.pRank_projSU_four_le_two (p := 2) (by norm_num) hk
        (Sec21.two_pow_mod_three_of_even he))
    exact c.false_of_bound hn hKq htype hKa le_rfl hαI hβI (fun F hF hFN => hbound F hF hFN)
  · exact hodd G L K a b c hK k ho h3k e hαI hβI

end Main

end CFSG.RankThree.PartTwo.Sec8.Hering418
