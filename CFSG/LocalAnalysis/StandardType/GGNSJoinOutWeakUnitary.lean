module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakDefs
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutOfWeak
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutLocalGen
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGReflectionBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

namespace NSJoin

section Proof

theorem nsWeakRk1Gen_of_nonUnitary' {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hBaseL1 : GGSecFiveL1PhanInput) (hBaseRk1 : GGSecFiveRk1PhanInput) (hJA2 : NSJA2InputOf T)
    (hNU : NSWeakNonUnitaryInputOf T) : NSWeakRk1InputOf T ∧ NSWeakGenInputOf T := by
  have key : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
        NSJoinGuardOf T p L Bs 𝒦 →
        ∀ K : Subgroup G, GGSecFiveWeakNbr p B Bs x L D J 𝒦 K →
          (∀ r ∈ ggAutomizer K Bs, GGIsReflection p r → GGRk1Concl p Bs K r) ∧
          K ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer K Bs), ⨆ (_ : GGIsReflection p r),
            ggRankOneIn K Bs r := by
    intro G _ _ p B Bs x L D J 𝒦 hcfg hns hguard K hw
    obtain ⟨⟨y, hK⟩, hKA⟩ := hw
    obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hguard
    have h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := hT3 hT
    obtain ⟨r₀, hr₀J, _r', _hr'J, hr₀refl, _hr'refl, _horder⟩ :=
      hJA2 G p B Bs x L D J 𝒦 ⟨hcfg, hns, ι, M, e, hpres, hT, hbig⟩
    have hC : GGConfig p B Bs x L D J := hcfg.1.1
    have hJL : J ≤ L := (hC.2.2.1.2.2.2.2.2.1.1).trans inf_le_left
    have hrLA : r₀ ∈ ggAutomizer L Bs := ggAutomizer_mono Bs hJL hr₀J
    have hr₀C : r₀ ∈ ggCoxRefl M e :=
      ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
        (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrLA) hr₀refl
    have h6₀ : Nat.card ↥(ggRankOneIn L Bs r₀) ≠ 6 := hbig r₀ hrLA hr₀C
    have hRkL : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → GGRk1Concl p Bs L r :=
      fun r hrA hrC => hBaseRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 L (Or.inl rfl) r hrA hrC
    have hseed : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ :=
      hBaseL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hbig L (Or.inl rfl) r₀ hrLA hr₀C
    have hnsK : ¬ GGSplitLie p K :=
      nsWeakNotSplit hcfg hns hpres h3 hrLA hr₀C h6₀ hseed (hRkL r₀ hrLA hr₀C) hK hKA
    have hKnbr : K = L ∨ ∃ y : G, GGNbr p B x D J y K := Or.inr ⟨y, hK⟩
    by_cases hU : GGMemberUnitary p Bs K
    ·
      have hRkK : ∀ r ∈ ggAutomizer K Bs, r ∈ ggCoxRefl M e → GGRk1Concl p Bs K r :=
        fun r hrA hrC => ggRk1Concl_unitary_nbr hcfg hpres hKnbr hnsK hU hrA hrC
      refine ⟨fun r hrA hrrefl => hRkK r hrA ?_, ?_⟩
      · exact ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3 (hKA hrA) hrrefl
      · have hL1K : ∀ r ∈ ggAutomizer K Bs, r ∈ ggCoxRefl M e →
            ggRankOnePerf Bs r = ggRankOneIn K Bs r :=
          fun r hrA hrC => ggL1_transfer_nbr hcfg hns hpres h3 hrLA hr₀C h6₀ hseed hKnbr hrA hrC
            (hRkL r₀ hrLA hr₀C) (hRkK r hrA hrC)
        have hL1L : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e →
            ggRankOnePerf Bs r = ggRankOneIn L Bs r :=
          fun r hrA hrC => ggL1_transfer_nbr hcfg hns hpres h3 hrLA hr₀C h6₀ hseed (Or.inl rfl) hrA
            hrC (hRkL r₀ hrLA hr₀C) (hRkL r hrA hrC)
        have hGenC : GGGenConcl M Bs K L 𝒦 e :=
          ggGenConcl_unitary_nbr hcfg hns hpres h3 hbig hKnbr hKA hnsK hU ⟨r₀, hrLA, hr₀C⟩ hL1K hL1L
        refine (le_of_eq hGenC).trans ?_
        refine iSup_le fun r => iSup_le fun hr => ?_
        have hr' : r ∈ ggAutomizer K Bs ∧ r ∈ ggCoxRefl M e := by simpa using hr
        exact (le_iSup (fun (_ : GGIsReflection p r) => ggRankOneIn K Bs r)
            (ggCoxRefl_isReflection (fun i => hpres.2 i) hr'.2)).trans
          ((le_iSup (fun (_ : r ∈ ggAutomizer K Bs) =>
              ⨆ (_ : GGIsReflection p r), ggRankOneIn K Bs r) hr'.1).trans
            (le_iSup (fun r => ⨆ (_ : r ∈ ggAutomizer K Bs),
              ⨆ (_ : GGIsReflection p r), ggRankOneIn K Bs r) r))
    · exact hNU G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, hT, hbig⟩ K ⟨⟨y, hK⟩, hKA⟩ hnsK hU
  exact ⟨fun G _ _ p B Bs x L D J 𝒦 hcfg hns hguard K hw => (key G p B Bs x L D J 𝒦 hcfg hns hguard K hw).1,
    fun G _ _ p B Bs x L D J 𝒦 hcfg hns hguard K hw => (key G p B Bs x L D J 𝒦 hcfg hns hguard K hw).2⟩

theorem nsNbrOutLocalGenInputOf_of_nonUnitary' {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput)
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hBaseL1 : GGSecFiveL1PhanInput) (hBaseRk1 : GGSecFiveRk1PhanInput)
    (hP : GGStdSubPrimeInput) (hPumpNbr : NSPumpNbrInputOf T) (hJA2 : NSJA2InputOf T)
    (hNU : NSWeakNonUnitaryInputOf T) : NSNbrOutLocalGenInputOf T :=
  let h := nsWeakRk1Gen_of_nonUnitary' hT3 hBaseL1 hBaseRk1 hJA2 hNU
  nsNbrOutLocalGenInputOf_of_weak' hL hT3 hBaseL1 hBaseRk1 hP hPumpNbr hJA2 h.1 h.2

theorem nsNbrOutLocalGenInputOf_of_nonUnitary {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hTAD : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → NSTypeAD M)
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hBaseL1 : GGSecFiveL1PhanInput) (hBaseRk1 : GGSecFiveRk1PhanInput)
    (hP : GGStdSubPrimeInput) (hPumpNbr : NSPumpNbrInput) (hJA2 : NSJA2InputOf T)
    (hNU : NSWeakNonUnitaryInputOf T) : NSNbrOutLocalGenInputOf T :=
  let h := nsWeakRk1Gen_of_nonUnitary' hT3 hBaseL1 hBaseRk1 hJA2 hNU
  nsNbrOutLocalGenInputOf_of_weak hL hTAD hT3 hBaseL1 hBaseRk1 hP hPumpNbr hJA2 h.1 h.2

end Proof

end NSJoin

end CFSG.StandardType

end
