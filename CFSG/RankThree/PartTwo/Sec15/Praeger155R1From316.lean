module

public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1FBarClosed

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec15.Sylow155R1
  CFSG.RankThree.PartTwo.Sec11

theorem step155HostE0WRes1TypeFBar_a7_from316
    (h316 : Sec19.Item316)
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hz : Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P) :
    Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P :=
  step155HostE0WRes1TypeFBar_a7_of_zExcl h316
    (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) hz

theorem step155HostE0WRes1TypeFBar_m22_from316
    (h316 : Sec19.Item316) (h159 : Item159R)
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hz : Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P) :
    Step155HostE0WRes1TypeFBar (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P :=
  step155HostE0WRes1TypeFBar_m22_of_zExcl h316
    (item148HJS14_of_wired Sec14.Ronan148M.item148S14_holds) h159 hz

end CFSG.RankThree.PartTwo.Sec15
