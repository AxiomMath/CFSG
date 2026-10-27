module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreLeHhat
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreHhatLeInter

namespace CFSG
end CFSG
open CFSG

/-! # The equation-(7) two-core equality -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch, `O2(H \inter M) = O2(Hhat)`. -/
public theorem secondCase_a7_twoCore_inter_eq_twoCore_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    twoCoreOf (c.H ⊓ w.M) = twoCoreOf c.Hhat :=
  le_antisymm
    (secondCase_a7_twoCore_inter_le_twoCore_Hhat
      hmin c w d hA7 hmodel)
    (secondCase_a7_twoCore_Hhat_le_twoCore_inter
      hmin c w d hA7 hmodel)

end CFSG.GorensteinWalter
