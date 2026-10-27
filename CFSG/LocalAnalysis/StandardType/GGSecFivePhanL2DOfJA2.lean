module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanL2DDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJA2PhanDDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupFork
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitWeylEquiv
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpNbr
import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJoinWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpRoute
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanFork
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanMemberL
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanJPoint
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPumpup
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanComm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggSecFiveL2PhanDInput_of_ja2
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGen : GGSecFiveGenPhanInput)
    (hPair : GGSecFivePhanPairInput) (hLB : GGLBalanceInput) (hJA2 : GGSecFiveJA2PhanDInput) :
    GGSecFiveL2PhanDInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hD hbig i j hij h2 hno
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  obtain ⟨r, hr, r', hr', hrr, hrr', h3⟩ :=
    hJA2 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hD hbig i j hij h2 hno
  obtain ⟨k, σ, hk, hM⟩ := hD
  obtain ⟨σ', hM', hi, hj⟩ :=
    ggDk_fork_of_disjPair hk hM hij h2 hno fun hk5 φ hφ =>
      ggDk_memberRoots_L_disjSupp_phan hGen hcfg hns hpres hle3 hbig hk5 hM φ hφ
  rw [← hi, ← hj] at hno ⊢
  obtain ⟨φ, hφ⟩ := ggDk_weylEquiv hM'
  have hss := ggDNoSameSupp_of_not_orbPair hk φ hφ hno
  obtain ⟨hcard, ε, hε, hΦL, hfix⟩ :=
    ggDk_memberRoots_L_phan hGen hcfg hns hpres hle3 hbig hk hM' φ hφ hss
  obtain ⟨I, v, θ, hI, hDv, hpJ, hIJ, hvI, hθ⟩ :=
    ggDk_stdSub_point_phan hcfg hpres hle3 hk φ hφ hε hΦL hfix hcard hr hr' hrr hrr' h3
  obtain ⟨t, t', hst, ht, ht', hmove⟩ :=
    ggDk_pumpup_sameSupp_phan hRk1 hLB hcfg hns hpres hle3 hbig hk φ hφ hε hfix hI hDv
      hpJ hIJ hθ hvI
  let K : Subgroup G := ggLayerClosure p (Subgroup.centralizer ({(v : G)} : Set G)) J
  have hKnbr : GGNbr p B x D J (v : G) K :=
    ggNbr_pumpup_of_moves (ggPumpupInput_of_lBalance hLB) hcfg.1.1 hpJ hDv ht' hmove
  have hk2 : 2 ≤ k := by omega
  obtain ⟨_, _, _, _, _, hγ, hγ'⟩ := id hst
  have hrC := mem_ggCoxRefl_of_ggDReflRoot e φ hφ hγ
  have hrC' := mem_ggCoxRefl_of_ggDReflRoot e φ hφ hγ'
  have hle := (ggDk_automizerJoin_le_of_signed hk φ hφ hε hΦL hfix hrC' hmove).trans
    (sup_le_sup_left ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr ht')) _)
  have hne : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ≠
      ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := fun h =>
    hst.ne hk2 (congrArg φ (e.injective (Subtype.ext h)))
  have htt : t * t' = t' * t := φ.injective (by rw [map_mul, map_mul, hst.commute hk2])
  have hcomm : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
      ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) *
        ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, htt]
  have hbr := ggRankOnePerf_comm_of_nbr_phan hL1 hRk1 hGen hPair hcfg hns hpres hle3 hbig
    hKnbr hle ht hrC ht' hrC' hne hcomm
  obtain ⟨w, hw, hw'⟩ := ggDk_sameSupp_conj hk hst
  have hc : ∀ (c : Fin k) (u : M.Group),
      w * (coxeterMatrix (isFiniteType_cartanD k)).simple c * w⁻¹ = φ u →
        φ.symm w * M.simple (σ' c) * (φ.symm w)⁻¹ = u := fun c u h => by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hφ, h]
  refine ggRankOnePerf_comm_of_conj_pair (ggAutomizerJoin_le_ggAutomizer L Bs 𝒦) e (φ.symm w)
    _ _ ?_
  rw [hc _ t hw, hc _ t' hw']
  exact hbr

end CFSG.StandardType

end
