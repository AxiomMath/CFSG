module

public import CFSG.RankThree.PartTwo.Sec15.Item152Res2ProofK
public import CFSG.RankThree.PartTwo.Sec15.Item152ResProof
public import CFSG.RankThree.PartTwo.Sec15.Item152StepsRoute

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof152Res2

variable {G : Type} [Group G] [Finite G]

theorem false_of_ctx152_of_confX
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    (h1411 : Item1411_1 A (lB A)) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hst : StellmacherKP) (hgen : KS152HJGen) (hAct : KS152HJAct)
    (hCover : Step152EndCover A (lB A)) (hX : Step152ConfX A (lB A)) {Y M X : Subgroup G}
    (hctx : Ctx152 A (lB A) Y M X) : False := by
  obtain ⟨c', hc', hdec, L', hL', hJ⟩ := exists_hj_of_sl25' h h148 h134 h48 h415 hctx
  obtain ⟨d, p, P, T, K, S, hD, hXN⟩ := hX Y M X hctx c' L' hc' hL' hJ hdec
  have hSG := hD.mem_scriptQPiStar_top hst h.isSimpleGroup
  have hSH := inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A) hD.norm_w h1411 hSG
  have h' : Sec14Std G A c' L' := { h with zpowers_mem_omegaA := hD.omega, mem_lA := hD.mem_lA }
  exact false_of_le_normalizer hctx hD hSH (hgen G A c' L' h' Y M X hctx d p P T K S hD hSH) hXN
    hAct hCover

end Proof152Res2

open Proof152Res2

variable {G : Type} [Group G] [Finite G]

theorem step152ConfThetaLeD_of_false {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hF : ∀ Y M X : Subgroup G, Ctx152 A LB Y M X → False) : Step152ConfThetaLeD A LB :=
  fun Y M X _ _ _ _ _ _ _ hpt _ _ _ _ _ => (hF Y M X hpt.ctx).elim

theorem step152ConfThetaNormD_of_false {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hF : ∀ Y M X : Subgroup G, Ctx152 A LB Y M X → False) : Step152ConfThetaNormD A LB :=
  fun Y M X _ _ _ _ _ _ _ hpt _ _ _ _ _ _ => (hF Y M X hpt.ctx).elim

theorem false_of_ctx152R_of_KX
    (h148 : Item148R) (h1411 : Item1411_1R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hst : CFSG.RankThree.PartTwo.StellmacherKP)
    (h142 : Item142AllS14) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (hKX : Step152ConfKXR)
    (h135 : Sec13.Item135) (hmult : KFacts.KS18Mult)
    (hWd : Step152ConfWdR) (hθ : Step152GenTheta) (hS : Step152GenS) (hX : Step152GenX)
    (hJ2 : KS152J2Gen) (hAct : KS152HJAct) (G : Type) [Group G] [Finite G] (A : Subgroup G)
    (c : G) (L : Subgroup G) (hR : Sec15R G A c L) :
    ∀ Y M X : Subgroup G, Ctx152 A (lB A) Y M X → False :=
  fun _ _ _ hctx => false_of_ctx152_of_confX hR.toSec14Std (h148 G A c L hR) (h1411 G A c L hR)
    h134 h48 h415 hst (kS152HJGen_of hθ hS hX hJ2) hAct (step152EndCoverR_of hX G A c L hR)
    (step152ConfXR_of_res h142 h1444 h146 hbot h134 h135 h48 h415 hmult hKX hWd G A c L hR) hctx

theorem step152ConfThetaLeDR_of_KX
    (h148 : Item148R) (h1411 : Item1411_1R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hst : CFSG.RankThree.PartTwo.StellmacherKP)
    (h142 : Item142AllS14) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (hKX : Step152ConfKXR)
    (h135 : Sec13.Item135) (hmult : KFacts.KS18Mult)
    (hWd : Step152ConfWdR) (hθ : Step152GenTheta) (hS : Step152GenS) (hX : Step152GenX)
    (hJ2 : KS152J2Gen) (hAct : KS152HJAct) : Step152ConfThetaLeDR :=
  fun G _ _ A c L hR => step152ConfThetaLeD_of_false (false_of_ctx152R_of_KX h148 h1411 h134 h48
    h415 hst h142 h1444 h146 hbot hKX h135 hmult hWd hθ hS hX hJ2 hAct G A c L hR)

theorem step152ConfThetaNormDR_of_KX
    (h148 : Item148R) (h1411 : Item1411_1R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (hst : CFSG.RankThree.PartTwo.StellmacherKP)
    (h142 : Item142AllS14) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (hKX : Step152ConfKXR)
    (h135 : Sec13.Item135) (hmult : KFacts.KS18Mult)
    (hWd : Step152ConfWdR) (hθ : Step152GenTheta) (hS : Step152GenS) (hX : Step152GenX)
    (hJ2 : KS152J2Gen) (hAct : KS152HJAct) : Step152ConfThetaNormDR :=
  fun G _ _ A c L hR => step152ConfThetaNormD_of_false (false_of_ctx152R_of_KX h148 h1411 h134 h48
    h415 hst h142 h1444 h146 hbot hKX h135 hmult hWd hθ hS hX hJ2 hAct G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
