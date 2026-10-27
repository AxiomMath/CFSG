module

public import CFSG.Sporadic.Co1Patterson.AmalgamIn
public import CFSG.Sporadic.Co1Patterson.AmalgamInnerMain
public import CFSG.Sporadic.Co1Patterson.AmalgamRigidEdge
public import CFSG.Sporadic.Co1Patterson.Generation
public import CFSG.Sporadic.Co1Block.TwoBCent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Monster.GMS CFSG.Open CFSG.LargeExtraspecial.S14
  CFSG.RankThree.PartTwo.Sec21
open CFSG.Blueprint (NativeSporadic.Co1)


theorem pattersonCo1Input_of_rigid (hHolt : HoltUniqueFixedPointSimple)
    (h35 : AschbacherSmith35Input)
    (h1 : AutInnerModAt aNC ((wT 2 : Vt) : NativeSporadic.Co1))
    (h2 : AutRigidAt aNC (vE : NativeSporadic.Co1) ((wT 2 : Vt) : NativeSporadic.Co1)) :
    PattersonCo1Input := by
  intro X _ _ t h
  have hw := notWeaklyClosed h35 h
  obtain ⟨Φ, hinj, hle⟩ := exists_hom_of_rigid h hw h1 h2
  have htop := eq_top_of_co1_le hHolt h (MonoidHom.ofInjective hinj).symm hle
  have hsurj : Function.Surjective Φ := MonoidHom.range_eq_top.1 htop
  exact ⟨(MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm⟩

theorem pattersonCo1Input_of (hHolt : HoltUniqueFixedPointSimple)
    (h35 : AschbacherSmith35Input) : PattersonCo1Input :=
  pattersonCo1Input_of_rigid hHolt h35 InnerNative.autInnerModAt_native autRigidAt_native

end CFSG.Sporadic.Co1Patterson
