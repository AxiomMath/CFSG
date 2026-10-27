module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPos
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
import CFSG.ClassicalInvolution.Phan.Standard
import CFSG.ClassicalInvolution.Phan.Center
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LieType.Steinberg.CentralExt.SUTwo
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryGenAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggMemberUnitary_baseRefl
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hLU : GGMemberUnitary p Bs L) : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e := by
  obtain ⟨K, _, _, _, f, n, ψ, hcard, hn4, hker, hrange, hdvd, hpos, hlab⟩ :=
    ggMemberUnitary_position hcfg (Or.inl rfl) hLU
  obtain ⟨ε, hεrefl, -⟩ := hpos
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have hA : ((ε (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs :=
    (ε (Equiv.swap a b)).2
  exact ⟨_, hA, ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
    (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hA) (hεrefl a b hab)⟩

section Nbr


theorem ggGenConcl_unitary_nbr {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hnsL : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {X : Subgroup G} (hXnbr : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) (hnsX : ¬ GGSplitLie p X)
    (hU : GGMemberUnitary p Bs X) (hrL : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e)
    (hL1Xall : ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → ggRankOnePerf Bs r = ggRankOneIn X Bs r)
    (hL1Lall : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → ggRankOnePerf Bs r = ggRankOneIn L Bs r) :
    GGGenConcl M Bs X L 𝒦 e := by
  unfold GGGenConcl
  have h3 := hle3
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 h3
  obtain ⟨K, _, _, _, f, n, ψ, hKcard, hn4, hker, hrange, hpdvd, hpos, -⟩ :=
    ggMemberUnitary_position_nbr hcfg hXnbr hU
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold GGTableBPosSU at hpos
  obtain ⟨ε, hεrefl, hεpair⟩ := hpos
  have hq : 2 ^ f ≠ 2 := by
    intro hf
    let a : Fin (m + 1) := blockIdx 0 (by omega : 0 + 2 ≤ m + 1) (0 : Fin 2)
    let b : Fin (m + 1) := blockIdx 0 (by omega : 0 + 2 ≤ m + 1) (1 : Fin 2)
    have hab : a ≠ b := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [a, b, blockIdx_val] at hv
      omega
    have hrXA : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈ ggAutomizer X Bs :=
      (ε (Equiv.swap a b)).2
    have hrXC : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
        (hXA hrXA) (hεrefl a b hab)
    have h6X : Nat.card (ggRankOneIn X Bs
        ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) = 6 := by
      rw [hεpair a b hab, ggMUG1_card_map K 2 f m ψ hKcard hker (by omega) ⟨0, by omega⟩,
        ggMUG1_card_su_two K 2 f hKcard, hf]
      norm_num
    obtain ⟨rL, hrLA, hrLC⟩ := hrL
    obtain ⟨a', ha'A, hra'⟩ := ggCoxRefl_conj_of_connected e hconn hrLC hrXC
    obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp (ggAutomizerJoin_le_top L Bs 𝒦 ha'A)
    have hperf : Nat.card (ggRankOnePerf Bs
        rL) =
        Nat.card (ggRankOnePerf Bs
          ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) := by
      have hmap := ggRankOnePerf_map_conj hg
        rL
      rw [← hra'] at hmap
      rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hL1X := hL1Xall ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) hrXA hrXC
    have hL1L := hL1Lall rL hrLA hrLC
    have h6perfX : Nat.card (ggRankOnePerf Bs
        ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) = 6 := by
      rw [hL1X]; exact h6X
    have h6inL : Nat.card (ggRankOneIn L Bs
        rL) = 6 := by
      rw [← hL1L, hperf]; exact h6perfX
    exact hbig rL hrLA hrLC h6inL
  refine le_antisymm ?_ ?_
  ·
    conv_lhs => rw [← hrange]
    rw [MonoidHom.range_eq_map, ← iSup_range_blockEmb2 hKcard hq m]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    let a : Fin (m + 1) := blockIdx (i : ℕ) (by omega) (0 : Fin 2)
    let b : Fin (m + 1) := blockIdx (i : ℕ) (by omega) (1 : Fin 2)
    have hab : a ≠ b := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [a, b, blockIdx_val] at hv
      omega
    have hrXA : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈ ggAutomizer X Bs :=
      (ε (Equiv.swap a b)).2
    have hrXC : ((ε (Equiv.swap a b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
        (hXA hrXA) (hεrefl a b hab)
    refine le_trans ?_ (le_iSup₂ (f := fun r (_ : r ∈ {r : MulAut ↥Bs |
        r ∈ ggAutomizer X Bs ∧ r ∈ ggCoxRefl M e}) => ggRankOneIn X Bs r) _ ⟨hrXA, hrXC⟩)
    rw [hεpair a b hab]
    rw [ggMUG1_block_eq K 2 f m i]
  ·
    exact iSup₂_le fun r _ => ggRankOneIn_le X Bs r

end Nbr

theorem ggGenUnitaryMemberInput_holds :
    GGGenUnitaryMemberInput := by
  intro hL1 G _ _ p B Bs x L D J 𝒦 hcfg hnsL ι M e hpres hle3 hbig X hX hnsX hU hLU
  exact ggGenConcl_unitary_nbr hcfg hnsL hpres hle3 hbig (hX.imp_right (hcfg.2.2.2.1.2 X))
    (fun r hr => ggAutomizer_le_ggAutomizerJoin hX hr) hnsX hU
    (ggMemberUnitary_baseRefl hcfg hpres hle3 hLU)
    (fun r hrA hrC => hL1 G p B Bs x L D J 𝒦 hcfg hnsL ι M e hpres hle3 hbig X hX r hrA hrC)
    (fun r hrA hrC => hL1 G p B Bs x L D J 𝒦 hcfg hnsL ι M e hpres hle3 hbig L (Or.inl rfl) r hrA hrC)

end CFSG.StandardType

end
