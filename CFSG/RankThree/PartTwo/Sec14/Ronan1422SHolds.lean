module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SStep
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFA6
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFA9
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFGL
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFSp
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFSpIn
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFJ3
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SKFJ3T
public import CFSG.RankThree.PartTwo.Sec13.Ronan41F135List

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG.RankThree.PartTwo.Sec13

theorem kf1422Sp48_holds : KF1422Sp48 := by
  refine ⟨kf1422Sp48_noE27, ?_, kf1422Sp48_center⟩
  intro Y _ _ J hJn hJ hCJ hY E hE hE27 hEJ P hP3 hEP hP
  obtain ⟨h81, hNc, hN9, hNΩ, hC⟩ := sp48_sylow_inputs hJn hJ hCJ hY hE hE27 hEJ hP3 hEP hP
  obtain ⟨hΩ, htr⟩ := sylow_facts_of_homocyclic hJn hE hE27 hEJ hEP hP h81 hNc hN9 hNΩ hC
  exact ⟨⟨⟨fun a b => Subtype.ext (hNc a a.2 b b.2)⟩⟩, hΩ, htr⟩

theorem kf1422J3_holds :
    KF1422J3 :=
  kf1422J3_of j3PermConfig_holds

section Holds

theorem step1422SIQR_holds (h431 : Sec4.Ronan431.Item4_31List42) (h1413 : Item1413CR)
    (h135 : Item135) (h142 : Concl142S14) (hbot : Item145BotS14) (h131 : Item131)
    (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5) : Step1422SIQR :=
  step1422SIQR_of h431 F135Last.componentList42_holds kf1422AutA6_holds kf1422A9Sp6_holds
    kf1422J3_holds kf1422GL42_holds kf1422Sp48_holds h1413 h135 h142 hbot h131 h48 h45

end Holds

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
