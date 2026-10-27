module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen3FCompDispatch
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltThreeNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r16_3FComp_of_std_of_r880
    {G : Type} [Group G] [Finite G]
    (D : Data G)
    (hstd : S168e3Std D)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D) :
    R16_3FComp D :=
  r16_3FComp_of_std_of_r880_of_alt67_three D hstd h880
    (fun {V₀ V L} {hV} c hcomp hs {n} hn hA hsum htrans =>
      s168e3_concl163F_of_alt_six_seven_sum_three_s_two
        (V₀ := V₀) (V := V) (L := L) (hV := hV) (n := n)
        (c := c) (hcomp := hcomp) (hs := hs) (hn := hn) (hA := hA)
        (hsum := hsum) (htrans := htrans))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
