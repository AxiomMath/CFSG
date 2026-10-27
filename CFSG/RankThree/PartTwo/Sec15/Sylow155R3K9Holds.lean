module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Rows
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Comp
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Ord
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Alt
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Ly
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9McLHe
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Co
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9RuHN
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9SuzTh
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9LieRows
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9LieThree
import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
import CFSG.RankThree.PartTwo.Sec4.Ronan148LUSa

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem k9J2Facts_holds :
    K9J2Facts :=
  ⟨Sporadic.J2.isSimpleGroup_J2, KFacts.KS14.Native.center_nativeJ2_eq_bot⟩

section Six


theorem k9Six : ∀ s ∈ sporadics42, RowOfK9 (Spor s) := by
  intro s hs
  simp only [sporadics42, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowOfK9_m11
  · exact rowOfK9_m12
  · exact rowOfK9_m22
  · exact rowOfK9_m23
  · exact rowOfK9_m24
  · exact rowOfK9_j1
  · exact rowOfK9_J2
  · exact rowOfK9_j3
  · exact rowOfK9_j4
  · exact rowOfK9_mcl
  · exact rowOfK9_ly
  · exact rowOfK9_hs
  · exact rowOfK9_he
  · exact rowOfK9_suz
  · exact rowOfK9_ru
  · exact rowOfK9_on
  · exact rowOfK9_co3
  · exact rowOfK9_co2
  · exact rowOfK9_hn
  · exact rowOfK9_th

end Six

section Holds


theorem k9Rows_holds : K9Rows := by
  have hJ : K9J2Facts := k9J2Facts_holds
  have hb : HardMathSupport.Solomon.Coordinator.LieOrderBridge :=
    HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  have hLSC : HardMathSupport.Solomon.Coordinator.LieSemisimpleCent :=
    HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
  have hLC : HardMathSupport.Solomon.Coordinator.LieComp.LieComp := Sec4.Ronan148L.lieComp_holds
  exact
    { one := by
        intro p e _ hp2 he
        by_cases hp3 : p = 3
        · subst hp3
          exact rowOfK9_projSL_two_three e he
        · exact k9_one_of_ne_three hJ hb hLSC hLC p e hp2 he hp3
      two_SL := k9_two_SL hJ hb hLSC hLC
      two_SU := k9_two_SU hJ hb hLSC hLC
      three := k9_three_of_bridge hb
      four_G2 := k9_four_G2 hJ hb hLSC hLC
      four_Sp := k9_four_Sp hJ hb hLSC hLC
      four_SL := k9_four_SL hJ hb hLSC hLC
      four_SU := k9_four_SU hJ hb hLSC hLC
      five := fun _ h5 h12 => rowOfK9_alternating h5 h12
      six := k9Six
      seven_SL2 := k9_seven_SL2 hJ hb hLSC hLC
      seven_SL3 := k9_seven_SL3 hJ hb hLSC hLC
      seven_SU3 := k9_seven_SU3 hJ hb hLSC hLC
      seven_Sp4 := k9_seven_Sp4 hJ hb hLSC hLC
      seven_SU4 := k9_seven_SU4 hJ hb hLSC hLC
      seven_G2 := k9_seven_G2 hJ hb hLSC hLC
      seven_D4 := k9_seven_D4 hJ hb hLSC hLC
      seven_Sz := k9_seven_Sz hJ hb hLSC hLC
      seven_F4 := k9_seven_F4 hJ hb hLSC hLC
      seven_Tits := k9_seven_Tits hJ hb hLSC hLC
      eight_SL5 := k9_eight_SL5 hJ hb hLSC hLC
      eight_SU5 := k9_eight_SU5 hJ hb hLSC hLC
      eight_SL6 := k9_eight_SL6 hJ hb hLSC hLC
      eight_SU6 := k9_eight_SU6 hJ hb hLSC hLC
      eight_SL7 := k9_eight_SL7 hJ hb hLSC hLC
      eight_Sp6 := k9_eight_Sp6 hJ hb hLSC hLC
      eight_Sp8 := k9_eight_Sp8 hJ hb hLSC hLC
      eight_OmegaPlus := k9_eight_OmegaPlus hJ hb hLSC hLC
      eight_OmegaMinus := k9_eight_OmegaMinus hJ hb hLSC hLC
      eight_SL4 := k9_eight_SL4 hJ hb hLSC hLC
      eight_Sp6_4 := k9_eight_Sp6_4 hJ hb hLSC hLC
      eight_SU5_4 := k9_eight_SU5_4 hJ hb hLSC hLC
      eight_SU5_8 := k9_eight_SU5_8 hJ hb hLSC hLC
      eight_F4 := k9_eight_F4 hJ hb hLSC hLC
      nine_SL3 := k9_nine_SL3
      nine_SU3 := k9_nine_SU3
      nine_G2 := k9_nine_G2_of_bridge hb
      nine_SL4 := k9_nine_SL4
      nine_SU4 := k9_nine_SU4 }

theorem res3K9_holds : Res3K9 :=
  res3K9_of_rows Sec4.Census.rank3II_4_2 k9Rows_holds

end Holds

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
