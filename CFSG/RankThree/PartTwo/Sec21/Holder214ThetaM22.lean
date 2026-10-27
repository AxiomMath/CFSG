module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EK2
public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaGen
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KD1913Aut

public section

namespace CFSG.RankThree.PartTwo.Sec21.Holder214Theta

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint
open CFSG.RankThree.PartTwo.KFacts
open Hering214Even

section M22


theorem m22E9NoInvol_holds : M22E9NoInvol := by
  intro F hF hF9 t ht ht2
  exact noInvol_of_fixSub CFSG.Sporadic.Schreier.m22_center_eq_bot'
    CFSG.Sporadic.Schreier.m22_mulAut_card
    (fun w hw => CFSG.LocalAnalysis.GLTheoremA.CatB.m22_fixSub_card w hw) F hF hF9 t ht ht2

theorem isElemAbelian_closure_m22xy :
    IsElemAbelian 3 (Subgroup.closure ({KS14.m22x, KS14.m22y} : Set NativeSporadic.M22)) :=
  ⟨⟨⟨fun a b => Subtype.ext (KS14.comm_of_mem_closure_m22xy a.2 b.2)⟩⟩,
    fun _ hg => KS14.pow_three_of_mem_closure_m22xy hg⟩

theorem evenThetaFacts_m22 : EvenThetaFacts NativeSporadic.M22 := by
  refine ⟨CFSG.Sporadic.Schreier.m22_center_eq_bot', fun σ hσ => ?_,
    ⟨_, isElemAbelian_closure_m22xy, KS14.card_closure_m22xy⟩, ?_⟩
  · obtain ⟨y, rfl⟩ := KS14.exists_conj_of_card_mulAut_le
      CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card σ
      ⟨1, by rw [pow_one]; exact hσ⟩
    exact ⟨y, rfl⟩
  · intro Ē Ū hĒ hĒ3 hĒ9 hŪ hŪ1 _ hcomm
    exact (false_of_noInvol (fun F _ hF hF9 t ht ht2 => m22E9NoInvol_holds F hF hF9 t ht ht2)
      hĒ hĒ3 hĒ9 hŪ hŪ1 hcomm).elim

end M22

end CFSG.RankThree.PartTwo.Sec21.Holder214Theta
