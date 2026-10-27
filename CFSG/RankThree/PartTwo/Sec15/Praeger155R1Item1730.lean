module

public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1From316

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec15.Sylow155R1
  CFSG.RankThree.PartTwo.Sec6

theorem step155HostE0WRes1TypeFBar_a7_split
    (h316 : Sec19.Item316)
    (hzL2 : Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type)
    (hzSU3 : Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenSU3Type) :
    Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenType :=
  step155HostE0WRes1TypeFBar_open_of_split
    (step155HostE0WRes1TypeFBar_a7_from316 h316 hzL2)
    (step155HostE0WRes1TypeFBar_a7_from316 h316 hzSU3)

theorem step155HostE0WRes1TypeFBar_m22_split
    (h316 : Sec19.Item316) (h159 : Item159R)
    (hzL2 : Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenL2Type)
    (hzSU3 : Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenSU3Type) :
    Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenType :=
  step155HostE0WRes1TypeFBar_open_of_split
    (step155HostE0WRes1TypeFBar_m22_from316 h316 h159 hzL2)
    (step155HostE0WRes1TypeFBar_m22_from316 h316 h159 hzSU3)

end CFSG.RankThree.PartTwo.Sec15
