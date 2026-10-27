module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.RankThree.PartTwo.KFacts.L34SL
public import CFSG.Quasithin.Background.A3FactsRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Assembly
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.Quasithin.Background.A3Structure318Defs
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.F1Weak
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.SmithC27Star
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.Blueprint Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem nonempty_mulEquiv_statedSL_of_isSL3Four
    {X : Type} [Group X] [Finite X]
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 4 ∧ Nonempty (X ≃* ↥(StatedSL 3 K)) := by
  obtain ⟨hSL3, hcenter⟩ := h
  obtain ⟨hquasi, hL3⟩ := hSL3
  haveI : Group.IsPerfect X := Group.isPerfect_def.mpr hquasi.1
  have hL3' : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 2 :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide : StatedLieTag.PSL ∈ classicalTags)).1 hL3
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hL3'
  letI := hKfield
  letI := hKfin
  haveI : CharP K 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hKcard
  obtain ⟨-, ⟨eSL⟩⟩ :=
    CFSG.QuasithinUnique.Ch1.triple_cover_linear (X := X) hcenter
      (p := 2) (f := 2) (by simpa using hKcard) e
      (fun E _ _ π hπ hcen hodd => by
        obtain ⟨s, hs, -⟩ :=
          CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated
            (n := 3) (by norm_num) hπ hcen hodd
        exact ⟨s, hs⟩)
  exact ⟨K, hKfield, hKfin, by simpa using hKcard, ⟨eSL⟩⟩

theorem pRank_three_eq_two_of_isSL3Four
    {X : Type} [Group X] [Finite X]
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨eSL⟩⟩ :=
    nonempty_mulEquiv_statedSL_of_isSL3Four h
  letI := hKfield
  letI := hKfin
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eSL]
  exact CFSG.Quasithin.R3c.pRank_three_statedSL_three_even (n := 2) (by norm_num)
    (by rw [hKcard]; norm_num)

theorem pRank_three_eq_two_of_mem_calC_of_isSL3Four
    {G : Type} [Group G] [Finite G] {M L : Subgroup G} (hL : L ∈ calC M)
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four (Bar2 L)) :
    CFSG.Open.pRank 3 L = 2 := by
  rw [← CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd (by norm_num) (by norm_num)]
  exact pRank_three_eq_two_of_isSL3Four h

theorem three_dvd_card_of_isSL3Four {X : Type} [Group X] [Finite X]
    (h : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four X) :
    3 ∣ Nat.card X := by
  have h3 : Nat.card (Subgroup.center X) = 3 := h.2
  exact h3 ▸ Subgroup.card_subgroup_dvd_card (Subgroup.center X)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
