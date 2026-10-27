module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHCRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHC
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanAData
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE

public section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

section Rows

theorem ggSecFive_not_split_of_not_tier1 {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hM : GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M) : ¬ GGSplitLie p L :=
  fun hs => hReg ⟨𝒦, hcfg, hs, ι, M, e, hpres, hM⟩

theorem ggSecFive_join_of_rows (hT : GGTBFixInput)
    (hSmall : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
        ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
        ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
          (∃ (n : ℕ) (e' : Fin n ≃ ι), (n = 3 ∨ n = 4) ∧ M = (CoxeterMatrix.A n).reindex e') →
            False)
    (hJD : GGSecFiveJoinPhanInput) (hJE : GGSecFiveJoinPhanEInput)
    (hB : GGSecFiveRowJoinOffQAt GGIsWeylMatrixB) (hF : GGSecFiveRowJoinOffQAt GGIsWeylMatrixF4)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J) (hrow : ¬ GGSecFivePhanARow p B Bs x L D J)
    (hQ : ¬ GGSecFiveQTwoCell p B Bs x L D J)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hsix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e) :
    ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K := by
  have hM := hpres.1
  rcases hM with ⟨n, e', hn, hM | ⟨hn2, hM⟩ | ⟨hn4, hM⟩⟩ | ⟨e', hM⟩ | ⟨e', hM⟩ |
    ⟨e', hM⟩ | ⟨e', hM⟩ | ⟨e', hM⟩
  ·
    haveI : Fintype ι := Fintype.ofEquiv (Fin n) e'
    have hcard : Fintype.card ι = n := by rw [Fintype.card_congr e'.symm, Fintype.card_fin]
    have hm3 : 3 ≤ n := hcard ▸ ggSecFive_three_le_card_of_tbfix hT hcfg hpres
    have hns : ¬ GGSplitLie p L :=
      ggSecFive_not_split_of_not_tier1 hcfg hReg hpres (Or.inl (Or.inl ⟨n, e', hm3, hM⟩))
    by_cases hn5 : 5 ≤ n
    · have hguard : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
        fun r hr hrc h6 => hsix ⟨hpres, Or.inl ⟨n, e', hn5, hM⟩, r, hr, hrc, h6⟩
      exact (hrow ⟨𝒦, hcfg, hns, ι, M, e, hpres, ⟨n, e', hn5, hM⟩, hguard⟩).elim
    · exact (hSmall G p B Bs x L D J 𝒦 hcfg hReg hns ι M e hpres ⟨n, e', by omega, hM⟩).elim
  · exact hB G p B Bs x L D J 𝒦 hcfg hReg hQ ι M e hpres ⟨n, e', hn2, hM⟩
  ·
    have hD : GGIsWeylMatrixD M := ⟨n, e', hn4, hM⟩
    have hns : ¬ GGSplitLie p L :=
      ggSecFive_not_split_of_not_tier1 hcfg hReg hpres (Or.inl (Or.inr hD))
    have hguard : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
      fun r hr hrc h6 => hsix ⟨hpres, Or.inr (Or.inl hD), r, hr, hrc, h6⟩
    exact hJD G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, hD, hguard⟩
  ·
    have hE : GGIsWeylMatrixE M := Or.inl ⟨e', hM⟩
    have hns : ¬ GGSplitLie p L := ggSecFive_not_split_of_not_tier1 hcfg hReg hpres (Or.inr hE)
    have hguard : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
      fun r hr hrc h6 => hsix ⟨hpres, Or.inr (Or.inr hE), r, hr, hrc, h6⟩
    exact hJE G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, hE, hguard⟩
  ·
    have hE : GGIsWeylMatrixE M := Or.inr (Or.inl ⟨e', hM⟩)
    have hns : ¬ GGSplitLie p L := ggSecFive_not_split_of_not_tier1 hcfg hReg hpres (Or.inr hE)
    have hguard : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
      fun r hr hrc h6 => hsix ⟨hpres, Or.inr (Or.inr hE), r, hr, hrc, h6⟩
    exact hJE G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, hE, hguard⟩
  ·
    have hE : GGIsWeylMatrixE M := Or.inr (Or.inr ⟨e', hM⟩)
    have hns : ¬ GGSplitLie p L := ggSecFive_not_split_of_not_tier1 hcfg hReg hpres (Or.inr hE)
    have hguard : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
      fun r hr hrc h6 => hsix ⟨hpres, Or.inr (Or.inr hE), r, hr, hrc, h6⟩
    exact hJE G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, hE, hguard⟩
  · exact hF G p B Bs x L D J 𝒦 hcfg hReg hQ ι M e hpres ⟨e', hM⟩
  ·
    haveI : Fintype ι := Fintype.ofEquiv (Fin 2) e'
    have hcard : Fintype.card ι = 2 := by rw [Fintype.card_congr e'.symm, Fintype.card_fin]
    have h3 := ggSecFive_three_le_card_of_tbfix hT hcfg hpres
    exfalso
    omega

theorem ggSecFiveCompatRestWResNInput_of_join_rows
    (hC : GGSecFiveCompatRestWResNJoinInput) (hT : GGTBFixInput)
    (hSmall : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
        ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
        ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
          (∃ (n : ℕ) (e' : Fin n ≃ ι), (n = 3 ∨ n = 4) ∧ M = (CoxeterMatrix.A n).reindex e') →
            False)
    (hJD : GGSecFiveJoinPhanInput) (hJE : GGSecFiveJoinPhanEInput)
    (hB : GGSecFiveRowJoinOffQAt GGIsWeylMatrixB) (hF : GGSecFiveRowJoinOffQAt GGIsWeylMatrixF4) :
    GGSecFiveCompatRestWResNInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT hW hd t n f ψ hpres hL hReg hrow
  have hR : GGSecFiveRestHyp p B Bs x L D J :=
    ⟨hcfg, hOp, hInn, hNT, hd, fun ⟨n', f', hs⟩ => hL hs.leviCase⟩
  obtain ⟨𝒦, hmax⟩ := exists_ggMaximalJoin hR hW
  have hcfg' : GGSecFiveRouteCfg p B Bs x L D J 𝒦 := ⟨hR, hW, hL, hmax⟩
  refine hC G p B Bs x L D J 𝒦 hcfg' hReg hrow t n f ψ hpres ?_
  by_cases hQ : GGSecFiveQTwoCell p B Bs x L D J
  · exact Or.inl hQ
  obtain ⟨ι, M, hM, e, hrefl⟩ := hmax.2.1
  have hpres' : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e := ⟨hM, hrefl⟩
  by_cases hsix : GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e
  · exact Or.inr (Or.inr ⟨ι, M, e, hsix⟩)
  refine Or.inr (Or.inl ?_)
  rw [ggSecFive_join_of_rows hT hSmall hJD hJE hB hF hcfg' hReg hrow hQ hpres' hsix]

end Rows

end CFSG.StandardType

end
