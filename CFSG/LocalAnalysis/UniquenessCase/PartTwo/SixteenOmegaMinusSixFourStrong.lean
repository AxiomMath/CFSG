module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixFourCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixFourFixers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenOmegaMinusSixFourSingular
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenStdNineTwentyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
public import Certificates.Certificate431004
public import Certificates.Certificate17430
public import Certificates.Certificate9726
public import CFSG.Adapters.Certificate43Check
public import CFSG.ClassicalGroups.Orthogonal.DiagonalTorusRankOddMinus
public import CFSG.ClassicalGroups.SpecialLinear.ComponentBorelQuotient
public import CFSG.ClassicalGroups.SpecialLinear.ComponentBorelSolvable
public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.ClassicalGroups.UnitaryFlag.SplitTorus
public import CFSG.GroupTheory.CommutatorCentralizerIn
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.NormalizerQuotientOddCover
public import CFSG.GroupTheory.NormalizerQuotientQuotient
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Lift
public import CFSG.LieType.SeitzGeneration.OuterLinearCat
public import CFSG.LinearAlgebra.RootGroupSL.SLFacts
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Solomon
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Overgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Glue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineSU
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyEightOq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SigmaCentZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.UEqZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Cover
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22r
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rm
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ro
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rp
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rr
public import CFSG.LocalAnalysis.WeakClosure81.FiveFourThree
public import CFSG.LocalAnalysis.WeakClosure81.FiveNineTwo
public import CFSG.LocalAnalysis.WeakClosure81.FiveTen
public import CFSG.Models.Transport
public import CFSG.Quasithin.Background.B69Comp2
public import CFSG.Quasithin.Background.B69Main
public import CFSG.Quasithin.Background.B69Struct
public import CFSG.Quasithin.Background.C116Two.FixMod
public import CFSG.Quasithin.Background.C116Two.NatLin2Linear
public import CFSG.Quasithin.Background.HFixSylBase
public import CFSG.Quasithin.Background.HModelTransp
public import CFSG.Quasithin.EmptyFaithful.S14113bMain
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG
public import CFSG.RankThree.GF2n.Smith81.OrthStmt
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm
public import CFSG.RankThree.PartOne.S11d.ThreeCompEasy
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
public import CFSG.RankThree.PartTwo.Sec3.TwoGroupPrimeFiveAction
public import CFSG.RankThree.PartTwo.Sec4.Item420
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

variable {G : Type} [Group G] [Finite G]

section


theorem s168e3_false_of_omegaMinus_six_four_natural_of_stronglyThreeEmbedded
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hN : NatOmegaMinus (lBar V₀ V hV L) (wTil V₀ V hV L) ⊥ 6 2)
    (hSP : IsStronglyPEmbedded 3 D.M) : False := by
  have hS : Sect16 D V₀ V L hV := ⟨c.setting, c.ne, c.conc⟩
  have hH : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hNat : NatOmegaMinus (lBar V₀ V hV L) ⊤ ⊥ 6 2 := by
    have h := hN
    rwa [hwT] at h
  obtain ⟨F, hFfield, hFfin, b, d, hF, hirr, ε, ψ, hcoords⟩ :=
    exists_natCoords_of_natOmegaMinus hNat
  have hF4 : Nat.card F = 4 := by
    rw [hF]
    norm_num
  obtain ⟨K, hKc, hbarK, hKN, hU4K, _hinj⟩ :=
    s168e3_exists_normal_cover_omegaMinus_six_four D c hs hN
  have h924 : R9_24X D := S168e3Std.r9_24X c.std
  have hAll : ∀ w ∈ V, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
    intro w hw hw1
    by_cases hw0 : w ∈ V₀
    · exact s168e3_uniqueMax_v0_of_omegaMinus_six_four_natural c hs hN hw0 hw1
    · have hne1 : mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) ≠ 1 := by
        intro h
        have h' : mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) =
            mkTil V₀ V hV 1 := h.trans (map_one _).symm
        rw [mkTil_eq_iff] at h'
        have hv : (IntMod.mk hV ⟨w, hw⟩).val = w := rfl
        rw [hv] at h'
        exact hw0 (by simpa using h')
      by_cases hQ : StatedQuadMinus 3 F b d
          (Multiplicative.toAdd (ψ ⟨mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩),
            Subgroup.mem_top _⟩)) = 0
      · exact s168e3_uniqueMax_of_exact_cover D hS (n := 2) (by norm_num) hF hirr ε ψ
          hcoords hKc hKN hbarK hU4K hw hne1 hQ h924 hSP
      · exact s168e3_uniqueMax_nonsingular_of_omegaMinus_six_four_natural c hs hN
          hF4 hirr ε ψ hcoords hw hQ
  have h129 : R129_1 D := r129_1_of_r127 D c.std.h127
  exact h129 V₀ V hH
    (s15_FiveTen_isTI_of_uniqueMax D hV hH.pairFacts.le_normalizer hAll)

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
