module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupFork
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitWeylEquiv
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpStdSub
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpRoute
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrbTwo
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggL2Split_D
    (hL1 : GGSecFiveL1CoxInput) (hKG : GGSecFiveKGPosInput) (hLB : GGLBalanceInput)
    (hSplit : GGSecFiveSplitNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) {i j : ι} (hij : i ≠ j) (h2 : M.M i j = 2)
    (hno : ¬ GGOrbPair L Bs 𝒦 M e i j) :
    ∀ a ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
    ∀ b ∈ ggRankOnePerf Bs ((e (M.simple j) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
      a * b = b * a := by
  obtain ⟨σ', hM', hi, hj⟩ :=
    ggDk_fork_of_not_orbPair hKG hcfg hsplit hpres hle3 hk hM hij h2 hno
  rw [← hi, ← hj] at hno ⊢
  obtain ⟨φ, hφ⟩ := ggDk_weylEquiv hM'
  have hss := ggDNoSameSupp_of_not_orbPair hk φ hφ hno
  obtain ⟨a₀, d₀, hD, hpt, hpJ, hJ⟩ := ggDk_stdSub_point hKG hcfg hsplit hpres hle3 hk hM' φ hφ
    (ggSecFiveRoute_bstar_eq_of_split hcfg hsplit) hss
  obtain ⟨t, t', hst, hcomm⟩ :=
    ggDk_comm_of_pumpPt hL1 hKG hLB hSplit hcfg hsplit hpres hle3 hk hM' φ hφ hss hD hpt hpJ hJ
  obtain ⟨w, hw, hw'⟩ := ggDk_sameSupp_conj hk hst
  have hc : ∀ (c : Fin k) (u : M.Group),
      w * (coxeterMatrix (isFiniteType_cartanD k)).simple c * w⁻¹ = φ u →
        φ.symm w * M.simple (σ' c) * (φ.symm w)⁻¹ = u := fun c u h => by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hφ, h]
  refine ggRankOnePerf_comm_of_conj_pair (ggAutomizerJoin_le_top L Bs 𝒦) e (φ.symm w) _ _ ?_
  rw [hc _ t hw, hc _ t' hw']
  exact hcomm

theorem ggSecFiveL2SplitInput_of_l1Cox
    (hL1 : GGSecFiveL1CoxInput) (hLB : GGLBalanceInput) (hSplit : GGSecFiveSplitNbrInput) :
    GGSecFiveL2SplitInput := by
  have hKG : GGSecFiveKGPosInput := ggSecFiveKGPosInput_holds
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 i j hij h2 hno
  by_cases hD : ∃ (k : ℕ) (σ : Fin k ≃ ι), 4 ≤ k ∧ M = (ggCoxeterMatrixD k).reindex σ
  · obtain ⟨k, σ, hk, hM⟩ := hD
    exact ggL2Split_D hL1 hKG hLB hSplit hcfg hsplit hpres hle3 hk hM hij h2 hno
  · exact absurd (ggOrbPair_of_label_two hKG hcfg hsplit hpres hle3 h2 hD) hno

end CFSG.StandardType

end
