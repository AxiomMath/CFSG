module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseEnnolaTwo
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankOne
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoAEightE
import CFSG.LocalAnalysis.StandardType.GGFrameTBHolds
import CFSG.LocalAnalysis.StandardType.GGFrameTBVacuous
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueOneOuter
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggRk1ConclEx_of_twE6Two_member_typeE (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput)
    (hT : GGSecFiveE6QTwoTimmesfeldInput) (hTB : GGTBFixInput) (hU62 : GGU62OuterDiagInput)
    (hWI : GGNbrInnerWeylInput) (hPU : GGPumpupInput) (hTCJ : GGTCJKnown)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hE : GGIsWeylMatrixE M)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hns : ¬ GGSplitLie p L) {r₀ : MulAut ↥Bs}
    (hr₀ : GGRk1ConclEx p Bs L r₀) (h6 : Nat.card (ggRankOneIn L Bs r₀) = 6)
    {X : Subgroup G} (hX : X ∈ 𝒦) (hnsX : ¬ GGSplitLie p X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs X) :
    ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r → GGRk1ConclEx p Bs X r := by
  have hlt : B < Bs := hcfg.lt_bstar_of_card_six hT hTB hU62 hWI
    FrameRoute.ggFrameTBNumerologyInput_holds FrameRoute.ggFrameTBVacuousInput_holds hPU
    FrameRoute.ggOuterThreeRankInput_holds hTCJ hpres hE hle3 hns hr₀ h6
    (hcfg.lt_bstar_of_twA_dvd_typeE hTB hWI FrameRoute.ggFrameTBNumerologyInput_holds
      FrameRoute.ggFrameTBVacuousInput_holds hRig hPU FrameRoute.ggOuterThreeRankInput_holds hTCJ hpres hE)
  exact ggRk1ConclEx_of_twE6Two_nbr_of_lt hRig hRk hcfg.1.1 (Or.inr (hcfg.2.2.2.1.2 X hX)) hnsX hmark hlt

theorem ggRk1ConclEx_of_twE6Two_member_unguarded (hRig : GGLabelRigidInput)
    (hRk : GGTwE6ThreeNbrRankInput) (hT : GGSecFiveE6QTwoTimmesfeldInput) (hTB : GGTBFixInput)
    (hU62 : GGU62OuterDiagInput) (hWI : GGNbrInnerWeylInput) (hPU : GGPumpupInput) (hTCJ : GGTCJKnown)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hns : ¬ GGSplitLie p L) (hTA : ¬ GGIsWeylMatrixA M) (hTD : ¬ NSJoin.NSTypeD M)
    (hunG : ¬ ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    (hbase : ¬ GGMemberUnitary p Bs L →
      ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs L r)
    {X : Subgroup G} (hX : X ∈ 𝒦) (hnsX : ¬ GGSplitLie p X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs X) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  have hE : GGIsWeylMatrixE M := GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 hle3 hTA hTD
  push Not at hunG
  obtain ⟨r₀, hr₀A, hr₀C, h6⟩ := hunG
  have hr₀ : GGRk1ConclEx p Bs L r₀ := by
    by_cases hUL : GGMemberUnitary p Bs L
    · obtain ⟨K, hKfield, hKfin, hKchar, f, n, ψ, hKcard, hn4, hker, hrange, hpf, hacts, hlab⟩ :=
        ggNSLie_cover_of_esu hUL
      letI : Field K := hKfield
      letI : Finite K := hKfin
      letI : CharP K 2 := hKchar
      exact ggRk1ConclEx_of_unitaryCover_nbr hcfg hpres (Or.inl rfl) hns hKcard hn4 hker hrange hpf
        hacts hlab hr₀A hr₀C
    · exact hbase hUL r₀ hr₀A hr₀C
  intro r hrA hrC
  exact ggRk1ConclEx_of_twE6Two_member_typeE hRig hRk hT hTB hU62 hWI hPU hTCJ hcfg hpres hE hle3 hns
    hr₀ h6 hX hnsX hmark r hrA (ggCoxRefl_isReflection hpres.2 hrC)

end CFSG.StandardType

end
