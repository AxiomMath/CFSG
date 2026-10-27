module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L3OddLA7
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem item1514_l3Odd_of
    (h148 : Item148R) (hbot : Item145BotS14) (h135 : Item135Simple) (h142 : Concl142R)
    (h138 : Item138N) (hgen : KS1517Gen) (hq0 : Step1517Q0) (hsimp : Step1517Simple)
    (hTL : Step1518TL) (hN : KS1518Norm) (h1444 : Item1444S14) (h146 : Item146S14)
    (hgen325 : Step1515LA7L325Gen) (h : Sec15R G A c L) (h152 : Item152 A (lB A))
    (h153 : Item153Main A (lB A)) (hobs : Claim153Obs A (lB A)) (h149 : Item149 A (lB A))
    (h1411 : Item1411_1 A (lB A)) (hloc : Claim1411Local A (lB A))
    (h1511 : Item1511 A (lB A) c L) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (hΩ : (scriptY0 A (lB A)).Nonempty → omegaA A = {Subgroup.zpowers c}) :
    Item1514 A (lB A) c L := by
  refine item1514_iff.mpr fun Y hY hm => ?_
  by_contra hce
  have hΩ' := hΩ ⟨Y, hY.prop⟩
  have hD := h.toSec13Data
  have hAHY : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G) :=
    le_inf (hD.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c))
      hY.prop.1.1.2
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨P, hP, hAP⟩ := Item134SylowBarProof.exists_isSylowOf_le hAHY hA3
  obtain ⟨hprod', -, hYL, hcases, -⟩ := h1511 p e he hiso Y hY.prop hm P hAP hP
  rcases hcases with hε | hY7
  ·
    have hctx : Ctx1514 A (lB A) c L Y :=
      { mem_y0Star := hY, meets := hm, not_concl := hce,
        concl1515 := ⟨p, e, inferInstance, he, hiso, hprod', hYL, hε, hΩ'⟩ }
    have h22 := not_isoLThreePi_two_two_of_ne_two hp2 he hiso
    have h1517 := step1517_at h135 h142 h138 hgen h152 h153 hobs h1411 hq0 hsimp h h22
    have h1516 := step1516_at h h153 hobs h149 h1411 hloc
    exact hp2 (step1518_at h1516 h1517 hTL hN h Y hctx p e he hiso)
  ·
    obtain ⟨hU, hno, hsimpL, hodd⟩ := step1515LA7_at h148 hbot h135 h142 hgen h152 h153 hobs
      h149 h1411 hloc h1511 h1444 h146 hgen325 h he hiso hΩ' hY hm hYL hY7
    exact hce (Or.inr (Or.inr ⟨hU, hY7, by rwa [inf_comm], hΩ', hno, hsimpL, hodd⟩))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd
