module

public import CFSG.RankThree.PartTwo.Sec15.Lempken155L3Cover1517
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155L3Cover1515
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Endgame
import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Step1520CoreComp

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Res1Cover

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof15Res6 CFSG.RankThree.PartTwo.Sec15.Proof1513Steps

variable {G : Type} [Group G] [Finite G]

theorem step1520R_of_item316
    (h316 : Sec19.Item316) : Step1520R :=
  step1520R_of_kfacts
    (item14_23R_of Sec4.rank3II_4_5 KFacts.kpSz (Sec14.item142R_of_wired item142AllS14_holds))
    (step1517R_of_item316 h316) Ronan138S.item138N_holds Y4Core.step1520CoreComp_holds

theorem step1521R_of_item316

    (h316 : Sec19.Item316) : Step1521R := by
  have h1517 := step1517R_of_item316 h316
  have hU : Step1521U :=
    step1521U_of_ctx
      (step1521UConj_of_qStar
        (by
          intro G _ _ A c L h Y hctx
          exact Sec16.exists_qStar_le_normalizer (item153Main_of_ctx1514 h316 h hctx)
            (claim153Obs_of_ctx1514 h hctx) hctx.mem_y0Star)
        item1411_1R_holds Proof148FourK.item146S14_holds
        (step1517Q0_of Ronan149.item1444S14_holds Proof148FourK.item146S14_holds
          Ronan149.item145BotS14_holds Ronan148M.concl142S14_holds)
        (step1521T_of (step1520R_of_item316 h316) h1517 Ronan138S.item138N_holds
          Proof148FourK.item146S14_holds Ronan149.item1444S14_holds
          (⟨S4Free.Stell34.stellmacherSzAll_proved.{0, 0}, KFacts.kpSz⟩ : StellmacherKP))
        (step1521CY_of_step1517R h1517))
      (by intro G _ _ A c L h Y hctx; exact claim153Normal_of_ctx1514 h hctx)
      (step1521Gen_of_step1517R h1517)
  intro G _ _ A c L h Y hctx
  exact rank3II_15_21_of h (step1520R_of_item316 h316 G A c L h) hU
    (claim153Normal_of_ctx1514 h hctx) (step1521Gen_of_step1517R h1517) Y hctx

theorem step1522R_of_item316

    (h316 : Sec19.Item316) : Step1522R := by
  have h1517 := step1517R_of_item316 h316
  intro G _ _ A c L h Y hctx
  exact rank3II_15_22_of h
    (Sec14.Ronan143Q.item14_24R_ofQ
      (item14_23R_of Sec4.rank3II_4_5 KFacts.kpSz (Sec14.item142R_of_wired item142AllS14_holds))
      Ronan148M.item143QS14_holds
      (step1424E_of Ronan148M.concl142S14_holds ks1424NonToral ks1424Torus)
      (step1424Core_of ks1424Core) G A c L h)
    (item153Main_of_ctx1514 h316 h hctx) (h1517 G A c L h)
    (step1522Hyp_of_item138N h1517 (step1518R_of_item316 h316) Ronan138S.item138N_holds)
    (step1522Conj_of_item138N h1517 Ronan138S.item138N_holds) Y hctx

theorem item1514_at_two
    (h316 : Sec19.Item316) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) {m : ℕ} (hm : 1 ≤ m)
    (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m)
    (hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A))
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Item1514 A (lB A) c L :=
  rank3II_15_14_of_steps (step1515_at_two h316 h hm hL hnPGL hWH)
    (step1519R_of_item316 h316 G A c L h) (step1521R_of_item316 h316 G A c L h)
    (step1522R_of_item316 h316 G A c L h)

theorem res1CoverL3_of_item316
    (h316 : Sec19.Item316) : Res1Omega1513.Res1CoverL3 := by
  intro G _ _ A c L h m hL hnPGL hWH Y hY hmeet
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : 1 ≤ m := one_le_of_isoLThreePi_two h hL
  rcases item1514_at_two h316 h hm hL hnPGL hWH Y hY hmeet with
    ⟨h1, h2, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨_, ⟨φ⟩⟩, -⟩
  · exact ⟨h1, h2⟩
  · exact (Proof1511.not_isoLThreePi_of_A7 φ hL).elim
  · have h25 := Sec19.Step1917EqProof.eq_of_isoLThreePi hm le_rfl hL
      (Or.inr ⟨by norm_num, ⟨φ⟩⟩)
    have h2 : 2 ∣ 5 ^ 1 := h25 ▸ dvd_pow_self 2 (by omega)
    norm_num at h2

end Res1Cover

theorem item1730_of_316_310
    (h316 : Sec19.Item316) (h310 : Sec6.Item3_10) : Sec17.Item1730 :=
  item1730_of_316_310_cover h316 h310 (Res1Cover.res1CoverL3_of_item316 h316)

end CFSG.RankThree.PartTwo.Sec15
