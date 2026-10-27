module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryPos
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal


@[expose] def GGSecFiveBaseReflInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) →
        ∃ r₀ ∈ ggAutomizer L Bs, r₀ ∈ ggCoxRefl M e

theorem ggSecFiveBaseReflInput_of_rows
    (hGenR : GGGenResidualMemberInput) : GGSecFiveBaseReflInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig
  by_cases hU : GGMemberUnitary p Bs L
  · obtain ⟨K, _, _, _, f, n, ψ, hcard, hn4, hker, hrange, hdvd, hpos, hlab⟩ :=
      ggMemberUnitary_position hcfg (Or.inl rfl) hU
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
  · by_contra hne
    have hne : ∀ r ∈ ggAutomizer L Bs, r ∉ ggCoxRefl M e := fun r hr hr' => hne ⟨r, hr, hr'⟩
    refine ggRouteCfg_ne_bot hcfg (le_bot_iff.mp ?_)
    calc L = ⨆ r ∈ {r : MulAut ↥Bs | r ∈ ggAutomizer L Bs ∧ r ∈ ggCoxRefl M e},
          ggRankOneIn L Bs r :=
          hGenR G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig L (Or.inl rfl) hns
            (fun h => hU h.2)
      _ ≤ ⊥ := iSup₂_le fun r hr => absurd hr.2 (hne r hr.1)

theorem ggSecFiveL1PhanInput_of_local (hRk1 : GGSecFiveRk1PhanInput)
    (hSolv : GGSecFiveAllFixedSolvInput) (ha₀ : GGLNoncyclicInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput)
    (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (hBase : GGSecFiveBaseReflInput) : GGSecFiveL1PhanInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig X hX r hrA hrC
  obtain ⟨r₀, hr₀A, hr₀C⟩ := hBase G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig
  have hrefl₀ : GGIsReflection p r₀ := ggCoxRefl_isReflection hpres.2 hr₀C
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hcfg.1.1.1 hcfg.1.1.2.2
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer (Bs : Set G)) :=
    SecFiveL1Solv.bstar_solvable_of_all_fixed_solvable ha₀ hLB hcfg hpJ
      (hSolv G p B Bs x L D J 𝒦 hcfg)
      (fun X hX => ggSecFive_outSolvable_of_member hSch hcfg hX)
  have hseed := ggL1_seed hRk1 ha₀ hsolv
    (ggSecFive_outSolvable_of_member hSch hcfg (Or.inl rfl)) hcfg hns hpres h3 hr₀A hrefl₀
    (hbig r₀ hr₀A hr₀C)
  exact ggL1_transfer hRk1 hcfg hns hpres h3 hr₀A hr₀C (hbig r₀ hr₀A hr₀C) hseed hX hrA hrC

end CFSG.StandardType

end
