module

public import CFSG.Quasithin.Background.FFCAssembly51
public import CFSG.Quasithin.Background.FFC3Part6
public import CFSG.Quasithin.Background.B5NonPart1
public import CFSG.Quasithin.Background.B5NonSQTK
public import CFSG.Quasithin.Background.B5P4
public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin

namespace FFC

theorem asB51_of_ffc'
    (h42 : AsB42) (hI16 : AsI16Cover) (hSp : AsB51NonsplitOffSp4)
    (hA36 : AsA36NoOddCover) (hSL3 : AsB51NonirrSL3) (hLn : AsB51NonirrLn) (h2 : B5.AsB51P2)
    (h5 : B5.AsB51P5) : AsB51 := by
  intro V _ _ hV G L h
  have hI := b51IrrInputs_of_ffc h42 hI16 hSp
  have h1 := B5.b51_part1' hI asA21SQTKSection hA36 hSL3 hLn hV h
  have h4 := B5.part4_of_inputs hI h2 hV h h1
  exact ⟨h1, ⟨B5.b51_part2_equiv L, h2 V hV G L h h1⟩, B5.part3_of_part1 hV h1, h4,
    h5 V hV G L h h1, part6_of_part4 h4⟩

end FFC

end CFSG.Quasithin
