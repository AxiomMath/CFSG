module

public import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdShape
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdHJCent
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4Gen
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdCoreA
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdSmall
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofProd
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Ronan148JStruct
public import CFSG.RankThree.PartTwo.Sec15.LiebeckY4Split

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

section TypeA


theorem exists_support_of_prodTypeA {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {M : Subgroup G} [(ker148 A M).Normal]
    (hM : M ∈ scriptY A) {J : Subgroup G} (hJle : J ≤ M)
    {V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)} (hset : ProdSetting (img148 A M J) V (img148 A M A))
    (hsup : img148 A M (deltaZero A (lB A) M) = img148 A M J ⊔ V)
    (hA : ProdTypeA (img148 A M J) V) :
    ∃ B : Subgroup G, IsHyperplane A B ∧ ¬ YBOne A (lB A) M B ∧
      ((deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B : Set G))).subgroupOf M).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤
        (J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) := by
  obtain ⟨BE, hBE, ha, hb, hcc⟩ := prodCoreA_holds fixA5_holds fixA6Cover_holds centJ2E9_holds _
    (img148 A M J) V (img148 A M A) hset hA
  obtain ⟨B, hB, rfl⟩ := exists_hyperplane_of_img h.isE27 hBE
  have hne : img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B : Set G))) ≠ ⊥ := by
    intro hbot
    have hDV : img148 A M (deltaZero A (lB A) M) ≤ V := by
      refine Ronan148J.img148_deltaZero_le_of_hyperplanes h.isE27 fun B' hB' R hR hRB' => ?_
      by_cases hBB : B' = B
      · subst hBB
        have h1 : img148 A M R ≤
            img148 A M (deltaZero A (lB A) (M ⊓ Subgroup.centralizer (B' : Set G))) :=
          img148_mono (le_deltaZero hR hRB')
        rw [hbot] at h1
        exact h1.trans bot_le
      · have hne : img148 A M B' ≠ img148 A M B := fun heq =>
          hBB (le_antisymm (le_of_img148_le h.isE27 hB'.1 hB.1 heq.le)
            (le_of_img148_le h.isE27 hB.1 hB'.1 heq.ge))
        refine hb (img148 A M B') (isHyperplane_img148 h.isE27 hB') hne (img148 A M R) ?_ ?_
        · rw [← hsup]
          exact (isInvQ_img148 ⟨hR, hRB'.trans inf_le_left⟩).1
        · rw [← Subgroup.le_centralizer_iff]
          exact Ronan148J.img148_le_centralizer (hRB'.trans inf_le_right)
    have hUV : img148 A M J ≤ V := le_sup_left.trans (hsup ▸ hDV)
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_fac hA.fac_left
    exact hab (Subtype.ext (hset.comm a a.2 b (hUV b.2)))
  refine ⟨B, hB, fun hY => hne ?_, ?_⟩
  · have := step148ProdBridge_holds G A c L h M hM B hB hY
    rw [hsup, hcc] at this
    exact le_bot_iff.mp this
  · refine map_le_of_img148_le ((deltaZero_le _).trans inf_le_left) hJle
      (img148_deltaZero_centralizer_le fun Q hQ hBQ => ha Q ?_ hBQ)
    rwa [← hsup]

end TypeA

section Assembly


theorem y4CoreMemSolvHJProdR_of_steps (h148 : Item148R) (h149 : Sec16.Item149S14)
    (hbot : Item145BotS14) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift) :
    Y4CoreMemSolvHJProdR := by
  intro G _ _ A c L h hall M hM hF hq J hJ hAJ
  have h14 := h.toSec14Std
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := hM.1.2
  letI := ker148_normal hAM
  obtain ⟨U, V, hsup, hc, hperf, hJU, htype⟩ :=
    step148ProdShape_of h148 h149 hbot G A c L h hall M hM hF hq J hJ hAJ
  subst hJU
  have hJM : J ∈ thetaComponentsIn M :=
    Y4Core.mem_thetaComponentsIn_of_item149 (h149 G A c L h14) hM.1 hJ
  have hset : ProdSetting (img148 A M J) V (img148 A M A) :=
    { comm := hc
      elem := (img148_isE27 h14.isE27).1
      card := (img148_isE27 h14.isE27).2
      norm := by
        rw [← hsup]
        exact img148_le_normalizer (Sec16.le_normalizer_deltaZero (A := A) (LB := lB A) M)
      perfect := hperf
      rank := fun F hF => Proof15Res8Prod.card_le_of_isElemAbelian_img148 h14 hAM hM.2 hF
      gen := by
        rw [← hsup]
        exact gen_img148 }
  rcases htype with hA | hH
  · obtain ⟨B, hB, hnot, hsupp⟩ :=
      exists_support_of_prodTypeA h14 hM.1 (le_of_mem_thetaComponentsIn hJM) hset hsup hA
    obtain ⟨J', hJ'M, -, K, hKJ', hKC, hKΔ, hKnc, hKns⟩ :=
      step148HJYBLiftB_of_gen h45 h48 step148HJYBGen_holds G A c L h hall M hM.1
        (Proof15Res8Solv.not_isSolvable_of_le (le_of_mem_thetaComponentsIn hJM)
          (isPerfect_of_mem_thetaComponentsIn hJM) (Y4Core.ne_bot_of_mem_thetaComponentsIn hJM))
        B hB hnot
    refine not_isSolvable_oPrimeResidual_delta_of
      (le_of_map_le_of_nonabelian hJM hJ'M hKJ' ?_ hKnc) hKΔ hKns
    exact (Proof15Res8Solv.map_subgroupOf_mono (hKΔ.le.trans (deltaZero_mono hKC)) _).trans hsupp
  · exact not_isSolvable_delta_of_prodTypeHJ hCore hPoint hKT hLift h45 h48 h hall hM.1 hJM hset
      hsup hH

theorem y4CoreMemSolvHJR_of_steps (h148 : Item148R) (h149 : Sec16.Item149S14)
    (hbot : Item145BotS14) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift) : Y4CoreMemSolvHJR :=
  y4CoreMemSolvHJR_of_split
    (y4CoreMemSolvHJQR_of_lift h148 h149 hbot
      (step148HJYBLift_of_gen h45 h48 step148HJYBGen_holds))
    (y4CoreMemSolvHJProdR_of_steps h148 h149 hbot h45 h48 hCore hPoint hKT hLift)

theorem y4CoreMemSolvR_of_route (h148 : Item148R) (h149 : Sec16.Item149S14)
    (hbot : Item145BotS14) (h134 : Item134) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift) :
    Y4CoreMemSolvR :=
  y4CoreMemSolvR_of_steps h148 h149 hbot h134 h48 hCore hPoint hKT hLift
    (y4CoreMemSolvHJR_of_steps h148 h149 hbot h45 h48 hCore hPoint hKT hLift)

end Assembly

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4
