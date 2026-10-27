module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA2FinishPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalA2Finish
open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
open CFSG.Open CFSG.LieType.Chevalley.RootOps
open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
open CFSG.StandardType.F4ExplicitPos.A2Actual CFSG.StandardType.F4ExplicitPos.RationalA2
open CFSG.StandardType.F4ExplicitPos.UnitaryPair
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups
variable {τ : Tag} {L : Type} [Field L] {ν : ℕ}

section Attachment

theorem component_eq_of_isComponentOf_of_fixed_quasisimple_of_perfect
    {G : Type*} [Group G] {C Ccent M Γ H N K : Subgroup G}
    (hC : C = Γ ⊓ Ccent) (hΓdef : Γ = ⁅M, M⁆) (hNdef : N = H ⊓ M)
    (hNperf : Group.IsPerfect ↥N) (hHcent : H ≤ Ccent)
    (hNq : CFSG.IsQuasisimple ↥N)
    (hK : CFSG.Assembly.IsComponentOf K C) (hKleH : K ≤ H)
    (hKq : CFSG.Assembly.IsQuasisimple ↥K) :
    K = N := by
  have hNleM : N ≤ M := hNdef ▸ inf_le_right
  have hNΓ : N ≤ Γ := by
    have : Group.IsPerfect ↥N := hNperf
    calc N = ⁅N, N⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hNleM hNleM
      _ = Γ := hΓdef.symm
  have hNcent : N ≤ Ccent := hNdef ▸ inf_le_left.trans hHcent
  have hNleC : N ≤ C := hC ▸ le_inf hNΓ hNcent
  have hKleΓ : K ≤ Γ := hK.1.trans (hC ▸ inf_le_left)
  exact RationalC3Attach.eq_of_isComponentOf_of_fixed_quasisimple_of_le_actual
    hNdef (hΓdef ▸ Subgroup.commutator_le_self M) hNleC hNq hK hKleH hKleΓ hKq

end Attachment

end CFSG.StandardType.F4ExplicitPos.RationalA2Finish

end

end
