module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
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
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
import CFSG.LocalAnalysis.StandardType.GGStdPosLocalConj
import CFSG.LocalAnalysis.StandardType.GGStdPosTableBPos
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

open scoped MatrixGroups

section Nbr


theorem ggSecFiveKGPosAt_splitNbr
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {X : Subgroup G} (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) (hXs : GGSplitLie p X) :
    ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
      StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n ∧
        ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = X ∧
        (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ p ∣ 2 ^ f - 1 ∧
        GGTableBPos p Bs X t n f ψ := by
  obtain ⟨t, n, f, ψ, hloc⟩ :=
    s2jn_ggKGPosRankStmt_holds G p B Bs x L D J 𝒦 (ggSecFiveRouteCfg'_of_routeCfg hcfg) X hX hXs
  obtain ⟨k, hstd⟩ := ggKGPos_exists_stdPos hloc
  have hloc' := ggKGPosLocalHyp_comp_conj hloc k
  exact ⟨t, n, f, ψ.comp (MulAut.conj k).toMonoidHom, hloc'.1.2.2.1, hloc'.1.2.2.2, hloc'.2.1.1,
    hloc'.2.1.2.1, hloc'.2.1.2.2.1, hloc'.2.1.2.2.2,
    ggKGPos_tableBPos_of_stdPos G p Bs X t n f _ hloc' hstd⟩

end Nbr

theorem ggSecFiveKGPosAt_splitMember
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) (hXs : GGSplitLie p X) :
    ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
      StatedLieAdmissible t n 2 f ∧ 3 ≤ bnRank t n ∧
        ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = X ∧
        (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ p ∣ 2 ^ f - 1 ∧
        GGTableBPos p Bs X t n f ψ :=
  ggSecFiveKGPosAt_splitNbr hcfg (hX.imp_right (hcfg.2.2.2.1.2 X)) hXs

theorem ggNotSplitLie_of_rk1_data
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} {r₀ r : MulAut ↥Bs} (hr₀C : r₀ ∈ ggCoxRefl M e) (hrC : r ∈ ggCoxRefl M e)
    (hRkL : GGRk1Concl p Bs L r₀) (hRkX : GGRk1Concl p Bs X r)
    (hL1L : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀)
    (hL1X : ggRankOnePerf Bs r = ggRankOneIn X Bs r) : ¬ GGSplitLie p X := by
  intro hs
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  have hAH : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs :=
    ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  obtain ⟨hpp, hp2⟩ := ggRouteCfg_prime hcfg
  obtain ⟨F, hF, hFfin, θ, -, hθinj, hθrange, -, -, hpF, -⟩ := hRkL
  obtain ⟨F', hF', hF'fin, θ', -, hθ'inj, hθ'range, -, hpF', -⟩ := hRkX
  obtain ⟨a, haA, hra⟩ := ggCoxRefl_conj_of_connected e hconn hr₀C hrC
  have hL1r₀ := hL1L
  have hL1r := hL1X
  have hc₀ : Nat.card (ggRankOnePerf Bs r₀) = Nat.card SL(2, F) := by
    rw [hL1r₀, ← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  have hc : Nat.card (ggRankOnePerf Bs r) = Nat.card SL(2, F') := by
    rw [hL1r, ← hθ'range]
    exact Nat.card_congr (MonoidHom.ofInjective hθ'inj).toEquiv.symm
  have hcr : Nat.card (ggRankOnePerf Bs r) = Nat.card (ggRankOnePerf Bs r₀) := by
    rw [hra]
    exact (ggRankOnePerf_conj_card_le (hAH haA) r₀).1
  have hFF : Nat.card F = Nat.card F' := ggSL2_card_inj (by rw [← hc₀, ← hc, hcr])
  have hq : 1 ≤ Nat.card F := le_of_lt Finite.one_lt_card
  have h1 : p ∣ Nat.card F + 1 := hpF hns
  have h2 : p ∣ Nat.card F - 1 := hFF ▸ hpF' hs
  have h3 : p ∣ 2 := by
    have h4 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub h1 h2
    have h5 : (Nat.card F + 1) - (Nat.card F - 1) = 2 := by omega
    rwa [h5] at h4
  have h6 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  have h7 : 2 ≤ p := hpp.two_le
  omega

theorem ggNotSplitLie_of_phan_refl
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGen : GGSecFiveGenPhanInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hrC : r ∈ ggCoxRefl M e) : ¬ GGSplitLie p X := by
  intro hs
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  obtain ⟨r₀, hr₀A, hr₀C⟩ : ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl M e := by
    by_contra hne
    refine ggRouteCfg_ne_bot hcfg (le_bot_iff.mp ?_)
    calc L = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e},
          ggRankOneIn L Bs r :=
          hGen G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) hns
      _ ≤ ⊥ := iSup₂_le fun r hr => absurd ⟨r, hr.1, hr.2⟩ hne
  exact ggNotSplitLie_of_rk1_data hcfg hns hpres hle3 hr₀C hrC
    (hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 L (Or.inl rfl) r₀ hr₀A hr₀C)
    (hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX r hrA hrC)
    (hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) r₀ hr₀A hr₀C)
    (hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig X hX r hrA hrC) hs

section Nbr


theorem ggPhanNbr_refl_of_split_nbr
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {K : Subgroup G} (hKnbr : ∃ y : G, GGNbr p B x D J y K)
    (hKA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦) (hKs : GGSplitLie p K) :
    ∃ r ∈ ggAutomizer K Bs, r ∈ ggCoxRefl M e := by
  obtain ⟨t, n, f, ψ, hadm, h3, hker, hrange, htag, hpf, hpos⟩ :=
    ggSecFiveKGPosAt_splitNbr hcfg (Or.inr hKnbr) hKs
  unfold GGTableBPos at hpos
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  have hrk : 2 ≤ (ggU t n f).D.rank := two_le_lieUniversal_rank t n 2 f Nat.prime_two hadm h3
  let i₁ : Fin (ggU t n f).D.rank := ⟨0, by omega⟩
  let r₀ : MulAut ↥Bs :=
    ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i₁) : ↥(ggAutomizer K Bs)) : MulAut ↥Bs)
  refine ⟨r₀, ?_, ?_⟩
  · exact (ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i₁)).2
  · exact ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (hKA (ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i₁)).2)
      (hεrefl i₁)

end Nbr

private theorem ggPhanNbr_refl_of_split
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {K : Subgroup G} (hK : K ∈ 𝒦) (hKs : GGSplitLie p K) :
    ∃ r ∈ ggAutomizer K Bs, r ∈ ggCoxRefl M e :=
  ggPhanNbr_refl_of_split_nbr hcfg hpres hle3 (hcfg.2.2.2.1.2 K hK) (fun r hr => ggAutomizer_le_ggAutomizerJoin (Or.inr hK) hr) hKs

theorem ggSecFiveNonSplitNbrInput_of_prim
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput) (hGen : GGSecFiveGenPhanInput) :
    GGSecFiveNonSplitNbrInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig K hK hKs
  obtain ⟨r, hrA, hrC⟩ := ggPhanNbr_refl_of_split hcfg hpres hle3 hK hKs
  exact ggNotSplitLie_of_phan_refl hL1 hRk1 hGen hcfg hns hpres hle3 hbig (Or.inr hK) hrA hrC hKs

end CFSG.StandardType

end
